module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0025
public import Formalism.PeriodIntegrals.NormRepChange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NlamFrameMem
section
noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.PairValDefs Matrix

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem coefX_sum (F : FlagG S r T) {y : S.V} (hy : y ∈ F.X) : ∑ a, F.coefX y a • F.e a = y := by
  have h : y ∈ Submodule.span E (Set.range F.e) := hy
  have hc : ∀ a, F.coefX y a = F.e_indep.repr ⟨y, h⟩ a := fun a => by
    simp [FlagG.coefX, h]
  simp_rw [hc]
  have key := F.e_indep.linearCombination_repr ⟨y, h⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by simp)] at key
  simpa using key

theorem coefX_eq_zero (F : FlagG S r T) {y : S.V} {b : ℕ} (hy : y ∈ F.Xa b) (a : Fin r) (ha : b ≤ a.val) :
    F.coefX y a = 0 := by
  have hy' : y ∈ Submodule.span E (F.e '' {i | i.1 < b}) := hy
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 hy'
  have hX : Finsupp.linearCombination E F.e l ∈ Submodule.span E (Set.range F.e) :=
    Submodule.span_mono (Set.image_subset_range _ _) hy'
  have hrep : F.e_indep.repr ⟨_, hX⟩ = l := F.e_indep.repr_eq rfl
  have hc : F.coefX (Finsupp.linearCombination E F.e l) a = l a := by
    simp [FlagG.coefX, hX, hrep]
  rw [hc]
  by_contra hne
  have h2 : a.1 < b := hl (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))
  omega

theorem e_mem_Xa (F : FlagG S r T) (i : Fin r) : F.e i ∈ F.Xa (i.val + 1) :=
  Submodule.subset_span ⟨i, Nat.lt_succ_self i.val, rfl⟩

theorem Xa_le_X (F : FlagG S r T) (j : ℕ) : F.Xa j ≤ F.X :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem z_mem_orth (F : FlagG S r T) : F.z ∈ orth S F.X := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x (hx : x ∈ Submodule.span E (Set.range F.e))
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, rfl⟩ := h
    exact F.z_orth a
  | zero => simp
  | add x w _ _ hx hw => simp [hx, hw]
  | smul c x _ hx => simp [hx]

theorem frame_castSucc (G : LFlag S r T) (i : Fin r) : frame G i.castSucc = G.fl.e i := by
  simp only [frame, FlagG.fvec, Fin.snoc_castSucc]

theorem frame_last (G : LFlag S r T) : frame G (Fin.last r) = G.fl.z := by
  simp only [frame, FlagG.fvec, Fin.snoc_last]

theorem nlam_frame_mem {Λ : Submodule (𝓞 E) S.V} (G : LFlag S r T) {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ G) :
    (∀ i : Fin r, n (G.fl.e i) - G.fl.e i ∈ G.fl.Xa i.val) ∧ n G.fl.z - G.fl.z ∈ G.fl.X := by
  obtain ⟨-, h1, h2⟩ := hn
  exact ⟨fun i => h1 i.val _ (e_mem_Xa G.fl i), h2 _ (z_mem_orth G.fl)⟩

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepExp (D : D7) : StepExp D := by
  unfold StepExp
  intro Λ T G n hn
  obtain ⟨hE, hZ⟩ := nlam_frame_mem G hn

  have hmem : ∀ b : Fin (D.R.rS + 1), ∀ c : Fin D.R.rS, b.val ≤ c.val →
      G.fl.coefX (n (frame G b) - frame G b) c = 0 := by
    intro b
    induction b using Fin.lastCases with
    | last =>
      intro c hc
      rw [Fin.val_last] at hc
      exact absurd c.is_lt (by omega)
    | cast i =>
      intro c hc
      rw [frame_castSucc]
      exact coefX_eq_zero G.fl (hE i) c (by rwa [Fin.coe_castSucc] at hc)
  have hX : ∀ b : Fin (D.R.rS + 1), n (frame G b) - frame G b ∈ G.fl.X := by
    intro b
    induction b using Fin.lastCases with
    | last => rw [frame_last]; exact hZ
    | cast i => rw [frame_castSucc]; exact Xa_le_X G.fl _ (hE i)
  have hfm : ∀ c b : Fin (D.R.rS + 1), b.val ≤ c.val →
      fmat D G n c b = if c = b then 1 else 0 := by
    intro c b hbc
    have h0 : (if h : c.val < D.R.rS then
        G.fl.coefX (n (frame G b) - frame G b) ⟨c.val, h⟩ else 0) = 0 := by
      split_ifs with h
      · exact hmem b ⟨c.val, h⟩ hbc
      · rfl
    simp only [fmat, h0, add_zero]
  refine ⟨fun i j => ⟨fun hji => ?_, fun hij => ?_⟩, fun b => ?_⟩
  · have hv := Fin.lt_iff_val_lt_val.1 hji
    rw [hfm i j (by omega), if_neg (ne_of_gt hji)]
  · subst hij
    rw [hfm i i le_rfl, if_pos rfl]
  · have hsum := coefX_sum G.fl (hX b)
    have h1 : ∀ i : Fin D.R.rS, fmat D G n i.castSucc b • frame G i.castSucc =
        (if i.castSucc = b then (1 : D.host.E) else 0) • frame G i.castSucc +
          G.fl.coefX (n (frame G b) - frame G b) i • G.fl.e i := by
      intro i
      have hc : (if h : (i.castSucc : Fin (D.R.rS + 1)).val < D.R.rS then
          G.fl.coefX (n (frame G b) - frame G b) ⟨(i.castSucc : Fin (D.R.rS + 1)).val, h⟩ else 0) =
            G.fl.coefX (n (frame G b) - frame G b) i := by
        rw [dite_eq_left (by simp)]
        rfl
      simp only [fmat, hc, add_smul, frame_castSucc]
    have h2 : fmat D G n (Fin.last _) b = if Fin.last _ = b then 1 else 0 := by
      simp [fmat]
    have h3 : ∑ c : Fin (D.R.rS + 1), (if c = b then (1 : D.host.E) else 0) • frame G c = frame G b := by
      simp [ite_smul]
    rw [Fin.sum_univ_castSucc] at h3
    rw [Fin.sum_univ_castSucc]
    simp_rw [h1, h2, Finset.sum_add_distrib, hsum]
    rw [add_right_comm, h3]
    abel

end PI.NRCW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NormRepMoveOfSteps
section
noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.PairValDefs Matrix IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem normRepMove_of_steps (D : D7) (u u' : D.what₂.Word) (hE : TermEqIff D u u')
    (h1 : StepExp D) (h2 : StepGram D) (h3 : StepGlob D) (h4 : StepLoc D) (h5 : StepTr D) :
    PI.NormRepChange.NormRepMove D u u' := by
  intro F0 Λ hΛ t _hrel F₁ F₂ hR1 hA1 hR2 hA2 w _hw
  obtain ⟨p1, e1⟩ := hR1
  obtain ⟨p2, e2⟩ := hR2
  have hDC : DCRel Λ (lf D F0) F₁ F₂ :=
    ((hE F0 Λ hΛ) ⟨F₁, p1⟩ ⟨F₂, p2⟩).mp (e1.trans e2.symm)
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hDC
  obtain ⟨hNu, hNe⟩ := h1 Λ (lf D F0) n hn
  obtain ⟨hMu, hMe⟩ := h1 Λ F₁ m hm
  have hG := h2 (lf D F0) F₁ F₂ n m (fmat D (lf D F0) n) (fmat D F₁ m) hn.1.1 hNe hMe hfr
  obtain ⟨A, B, hA, hB, hZ, hs⟩ := core_Z _ _ _ _ hNu hMu hG
  refine ⟨A, B, hA, hB, hZ, ?_⟩
  rw [hs]
  obtain ⟨_, ⟨_, _, hLift0, hConv0⟩, hXS0⟩ := hΛ
  obtain ⟨hLift1, _, hConv1, hXS1⟩ := p1
  have hglob : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E,
      (o : D.host.E) = (sgUp (fmat D (lf D F0) n) + sgUp (fmat D F₁ m)) * δ := by
    intro δ hδ
    obtain ⟨o1, ho1⟩ := h3 Λ (lf D F0) n hn hXS0 hLift0.1 δ hδ
    obtain ⟨o2, ho2⟩ := h3 Λ F₁ m hm hXS1 hLift1.1 δ hδ
    exact ⟨o1 + o2, by rw [add_mul, ← ho1, ← ho2]; norm_cast⟩
  have hloc := h4 Λ (lf D F0) F₁ F₂ n m hn hm hfr hConv0 hConv1 hA1 hA2 hLift0.1 hLift1.1
  obtain ⟨k, hk⟩ := h5 _ hglob hloc
  exact psiInf_of_trace (gS D) _ _ k hk

end PI.NRCW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.StepGram
section
noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.PairValDefs Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepGram (D : D7) : StepGram D := by
  intro T T' G G₁ G₂ n m N M hn hN hM hG
  unfold ZhatL Zhat brS frame at *
  have hiso : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hn
  funext a b

  have hL : ∑ c, star (N c a) * (VS D).hT (G.fl.fvec c) (G₂.fl.fvec b) =
      (VS D).hT (n (G.fl.fvec a)) (G₂.fl.fvec b) := by
    rw [hN a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply]
  have hR : ∑ c, (VS D).hT (G.fl.fvec a) (G₁.fl.fvec c) * M c b =
      (VS D).hT (G.fl.fvec a) (m (G₁.fl.fvec b)) := by
    rw [hM b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  change ∑ c, star (N c a) * (VS D).hT (G.fl.fvec c) (G₂.fl.fvec b) =
    ∑ c, (VS D).hT (G.fl.fvec a) (G₁.fl.fvec c) * M c b
  rw [hL, hR, hG b, hiso]

end PI.NRCW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.TraceIntOfMulDd
section
noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gS_ne_zero (D : D7) : gS D ≠ 0 := by
  show D.host.g 0 * D.host.g 1 ≠ 0
  exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

theorem coe_algebraMap_OF (D : D7) (δ : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) δ : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (δ : D.host.F) := rfl

theorem trace_int_of_mul_dd (D : D7) (x : D.host.E)
    (hx : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * δ) :
    ∃ k : ℤ, Algebra.trace ℚ D.host.E x = k := by
  have ha : ∀ δ ∈ differentIdeal ℤ (𝓞 D.host.F),
      ∃ a : 𝓞 D.host.F, (a : D.host.F) = (δ : D.host.F) * Algebra.trace D.host.F D.host.E x := by
    intro δ hδ
    have hmem : algebraMap D.host.F D.host.E (δ : D.host.F) ∈ ddS D := by
      unfold ddS
      rw [FractionalIdeal.mem_coeIdeal]
      exact ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) δ, Ideal.mem_map_of_mem _ hδ, coe_algebraMap_OF D δ⟩
    obtain ⟨o, ho⟩ := hx _ hmem
    have htr : Algebra.trace D.host.F D.host.E (o : D.host.E) = (δ : D.host.F) * Algebra.trace D.host.F D.host.E x := by
      rw [ho, mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
    have hint : IsIntegral ℤ (Algebra.trace D.host.F D.host.E (o : D.host.E)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
    rw [htr] at hint
    exact ⟨⟨_, hint⟩, rfl⟩
  have hdual : Algebra.trace D.host.F D.host.E x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) := by
    rw [← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)), ← coeIdeal_differentIdeal ℤ ℚ D.host.F,
      FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot)]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    obtain ⟨a, ha'⟩ := ha y' hy'
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨a, by rw [mul_comm]; exact ha'⟩
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0)] at hdual
  obtain ⟨k, hk⟩ := hdual 1 (FractionalIdeal.one_mem_one _)
  refine ⟨k, ?_⟩
  have h1 : Algebra.traceForm ℚ D.host.F (Algebra.trace D.host.F D.host.E x) 1 = Algebra.trace ℚ D.host.F (Algebra.trace D.host.F D.host.E x) := by
    rw [Algebra.traceForm_apply, mul_one]
  rw [← Algebra.trace_trace (S := D.host.F), ← h1, ← hk]
  simp

theorem stepTr (D : D7) : StepTr D := by
  intro y hy hP
  have hg0 : (gS D : D.host.E) ≠ 0 := by exact_mod_cast gS_ne_zero D
  have hint : ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = y / (gS D : D.host.E) * δ := by
    intro δ hδ
    obtain ⟨o, ho⟩ := hy δ hδ
    have hδint : ∃ d' : 𝓞 D.host.E, (d' : D.host.E) = δ := by
      unfold ddS at hδ
      obtain ⟨d', -, hd'⟩ := (FractionalIdeal.mem_coeIdeal _).mp hδ
      exact ⟨d', hd'⟩
    obtain ⟨d', rfl⟩ := hδint
    have hval : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
        P.valuation D.host.E (y / (gS D : D.host.E) * d') ≤ 1 := by
      intro P
      by_cases hPg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
      · rw [map_mul]
        exact mul_le_one' (hP P hPg) (P.valuation_le_one d')
      · have h1 : P.valuation D.host.E ((gS D : ℕ) : D.host.E) = 1 := by
          have h2 := (P.valuation_eq_one_iff_notMem (K := D.host.E)).mpr hPg
          simpa using h2
        have e : y / (gS D : D.host.E) * d' = (y * d') / (gS D : D.host.E) := by ring
        rw [e, map_div₀, h1, div_one, ← ho]
        exact P.valuation_le_one o
    obtain ⟨o', ho'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (h := hval)
    exact ⟨o', ho'⟩
  obtain ⟨k, hk⟩ := trace_int_of_mul_dd D (y / (gS D : D.host.E)) hint
  refine ⟨k, ?_⟩
  have e : y = ((gS D : ℚ)) • (y / (gS D : D.host.E)) := by
    rw [Algebra.smul_def, map_natCast]
    field_simp
  rw [e, LinearMap.map_smul, hk, smul_eq_mul]

end PI.NRCW
end
end

