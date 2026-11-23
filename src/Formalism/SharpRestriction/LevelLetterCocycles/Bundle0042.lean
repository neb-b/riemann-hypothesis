module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0027
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0041
public import Development.AutomorphicArithmetic.BlochKatoExtensions.BkExtHolds
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0025
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.BoundedNumeratorPowerSummability
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondLiftAtSituation

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfInputs
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Module IsLocalRing

def levBOfSit {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ}
    {LL : FinExt l} {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (finrank ℚ_[l] ↥(K0 K))} {E : EtSit P AI K s LL h W}
    (S : CmpSit P AI K s LL h E) : LevB W where
  levB := S.tie.levB
  mem := S.tie.levB_mem
  supp := S.tie.levB_supp


set_option maxHeartbeats 1000000 in
theorem local_theorem_of_inputs (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (C : ℝ)
    (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F)
    (hP6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (hPr2a : Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F)
    (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.lem3 D HW F)
    (h3 : adm3 D HW F) (h4 : ArchimedeanSignatureMatching D HW F C) (h7 : adm7 D HW F Cm)
    (h8 : adm8 D HW F) (h9a : adm9 D HW F) (h10 : adm10 D HW F) (h14 : adm14 D)
    (hDdR : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris ((D.loc l).PD K) ↥LL.1)
    (h9 : Formalism.MainNotions.LocalSituation.adm9 D HW F) (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F)
    (hUG : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l →
      ∃ e, UnitGen ((HW l).W K 1 LL h.2.2) e) : Conclusion1 D 800 := by
  refine local_theorem_of_cyclotomic_lift D.loc id (fun l _ K LL h => (HW l).W K 1 LL h.2.2)
    (fun l _ K LL h _ h5 hz => ?_) (Formalism.MainNotions.UnusedSlot80.base_change_every_theory D.loc)
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
  refine crystalline_lifting_second_form (brHyp2_of_rec (D.loc l) h h5 _ ((HW l).W_s K 1 LL h.2.2)
    (hP5 l K 1 LL h.2.2) (hP6 l K 1 LL h.2.2) (hP9 l K 1 LL h.2.2) (hPr2a l K 1 LL h.2.2)
    (h3.1 l K 1 LL h.2.2) (h4 l K 1 LL h.2.2)
    (h7 l K LL h h5).1 (h9a l K LL h h5) (h10 l K LL h h5) (h14 l K LL) ?_)
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨e, he⟩ := hUG l K LL h h5
  refine ⟨e, he, UpperTheory.Prune.bkExt_holds D HW F h9 hFont l K LL h h5 e he, fun hR => ?_⟩
  have hV := valRing_rec (D.loc l) LL
  have hpl := (D.loc l).PD_p K
  have : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  have : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.BasicNotions.Examples₂.LB.OL_frac LL
  have hpm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ maximalIdeal ↥(OL LL) :=
    (mem_maximalIdeal _).2 (not_isUnit_p ((HW l).W K 1 LL h.2.2) hV)
  have hpm' : ((l : ℕ) : ↥(OL LL)) ∈ maximalIdeal ↥(OL LL) := by
    have h' := hpm
    rwa [hpl] at h'
  have hp0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have h0' := congrArg (algebraMap ↥(OL LL) ↥LL.1) h0
    rw [map_natCast, map_zero] at h0'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h0'
  have : IsAdicComplete (maximalIdeal ↥(OL LL)) ↥(OL LL) :=
    Formalism.MainNotions.N.Ln03.Pf.complMax_holds ↥(OL LL) l hpm' hp0 (complete_OL LL)
  obtain ⟨uZ, huZ, hutie⟩ := Formalism.MainNotions.N.Ln03.Pf.uTieRec_holds D HW l K LL h h5
  have hrich : ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ finrank ℚ_[l] ↥(K0 K)) := by
    obtain ⟨ζ, hζ⟩ := hz
    exact ⟨ζ, by rw [hpl]; exact hζ⟩
  have h5' : 5 ≤ ((D.loc l).PD K).p := by rw [hpl]; exact h5
  refine realised2_pf (K := ↥K.1) (W := (HW l).W K 1 LL h.2.2) (levBOfSit ((Cm l).C K 1 LL h.2.2)) hR e uZ
    (ιZrec (D.loc l) K LL)
    ?_ ?_ ?_ ?_ ?_ ?_ ((HW l).W_s K 1 LL h.2.2) (hP4 l K 1 LL h.2.2) ?_ ?_ (hP3 l K 1 LL h.2.2)
    (hP9 l K 1 LL h.2.2) (hP5 l K 1 LL h.2.2) ?_ ?_ ?_ hV (unram_of_caseA h) hpm hrich huZ hutie he ?_ h5'
  · exact ((Cm l).C K 1 LL h.2.2).tie.levN_eq
  · exact ((Cm l).C K 1 LL h.2.2).tie.cmp_eq
  · exact ((Cm l).C K 1 LL h.2.2).tie.levB_φ
  · exact ((Cm l).C K 1 LL h.2.2).tie.levB_Γ
  · exact ((Cm l).C K 1 LL h.2.2).tie.lev_Γ
  · exact ((Cm l).C K 1 LL h.2.2).tie.lev_φ
  · exact (h7 l K LL h h5).2
  · exact h8 l K LL h h5
  · exact hLem3 l K 1 LL h.2.2
  · exact hDdR l K LL h
  · exact (h14 l K LL).1
  · exact Formalism.MainNotions.LiftingTheory.gen_one_crys _

theorem logb_nat_nonneg_sk (p h : ℕ) (hp : 11 ≤ p) : 0 ≤ Real.logb p (h : ℝ) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  · apply Real.logb_nonneg
    · have : (11 : ℝ) ≤ p := by exact_mod_cast hp
      linarith
    · exact_mod_cast hh

theorem corollary_monotone_in_constant (D : D7) (C C' : ℝ) (h : C ≤ C') (H : Conclusion2 D C) : Conclusion2 D C' := by
  intro l _ K LL n _ emb
  have H' := H l K LL n emb
  intro hL h11 T₁ T₂ F hG h1 h2 hF r b w S η j typ sz hr hj hn hJ hT hb hC
  obtain ⟨mm, k, e1, e2, e3⟩ := H' hL h11 T₁ T₂ F hG h1 h2 hF r b w S η j typ sz hr hj hn hJ hT
    (le_trans (by gcongr) hb) hC
  refine ⟨mm, k, e1, e2, le_trans e3 ?_⟩
  have hp : (11 : ℝ) ≤ ((D.loc l).PD K).p := by exact_mod_cast h11
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h ?_) ?_) ?_) ?_
  · positivity
  · positivity
  · have := logb_nat_nonneg_sk ((D.loc l).PD K).p (hCor b w S η sz) h11
    have h3 : (0 : ℝ) ≤ (((D.loc l).PD K).p : ℝ) - 1 := by linarith
    positivity
  · positivity

theorem corollary_local_exists_constant : ∃ C₀ : ℝ, ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (C : ℝ),
    Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm → Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm → Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F →
    Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F → Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F → Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F → Formalism.MainNotions.DeltaInvariantLattices.lem3 D HW F →
    adm3 D HW F → ArchimedeanSignatureMatching D HW F C → adm7 D HW F Cm → adm8 D HW F → adm9 D HW F →
    adm10 D HW F → adm12 D → adm14 D →
    (∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris ((D.loc l).PD K) ↥LL.1) →
    Formalism.MainNotions.LocalSituation.adm9 D HW F → Formalism.MainNotions.InvariantsGenerators.LitFont D HW F →
    (∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l →
      ∃ e, UnitGen ((HW l).W K 1 LL h.2.2) e) →
    Conclusion1 D 800 ∧ ∀ C₂ : ℝ, C₀ ≤ C₂ → Conclusion2 D C₂ := by
  obtain ⟨C', h1', h'⟩ := corollary_of_Theorem_E
  refine ⟨max C' (4 * 800), fun D HW F Cm C hP3 hP4 hP5 hP6 hP9 hPr2a hLem3 h3 h4 h7 h8 h9a h10 h12 h14
    hDdR h9 hFont hUG => ?_⟩
  have hp1 := local_theorem_of_inputs D HW F Cm C hP3 hP4 hP5 hP6 hP9 hPr2a hLem3 h3 h4 h7 h8 h9a h10 h14 hDdR h9 hFont hUG
  refine ⟨hp1, fun C₂ h2 => ?_⟩
  refine corollary_monotone_in_constant D _ C₂ h2 ?_
  refine h' D 800 (by norm_num) hp1 h12 ?_
  intro l _ K LL n _ emb T₁ T₂ F h1 h2 hF i A hA' τ hτ a ha
  exact hA' τ hτ a ((h14 l K LL).1 T₁ T₂ F h1 h2 hF τ a ha)

end Formalism.MainNotions.N.Ln03
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SecInTransport
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

theorem secIn_zero {a : ZMod n} {e d : ℕ} (cond : (ℕ → ℤ) → (Fin d → O) → Prop) :
    SecIn W a e cond (fun _ => 0) :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun k => by simp⟩

theorem secIn_add {a : ZMod n} {e d : ℕ} {cond : (ℕ → ℤ) → (Fin d → O) → Prop} {F F' : Fin d → W.EE}
    (h : SecIn W a e cond F) (h' : SecIn W a e cond F') : SecIn W a e cond (F + F') := by
  obtain ⟨I, g, c₀, α, hg, hF⟩ := h
  obtain ⟨I', g', c₀', α', hg', hF'⟩ := h'
  refine ⟨I + I', Fin.append g g', Fin.append c₀ c₀', Fin.append α α', fun i => ?_, fun k => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; exact hg i
    · simp only [Fin.append_right]; exact hg' i
  · rw [Pi.add_apply, hF k, hF' k, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem inFr_mulA {a : ZMod n} {num den : LetA O n} {f : W.EE} (h : InFr W a num den f) {c : LetA O n}
    (hc : c ∈ W.AΔ) : InFr W a num den (algebraMap (LetA O n) W.EE c * f) := by
  obtain ⟨u, hu, hf⟩ := h
  refine ⟨c * u, W.AΔ.mul_mem hc hu, ?_⟩
  rw [mul_left_comm, hf, ← map_mul]
  congr 1; ring

theorem inFr_add {a : ZMod n} {num den : LetA O n} {f f' : W.EE} (h : InFr W a num den f)
    (h' : InFr W a num den f') : InFr W a num den (f + f') := by
  obtain ⟨u, hu, hf⟩ := h
  obtain ⟨u', hu', hf'⟩ := h'
  refine ⟨u + u', W.AΔ.add_mem hu hu', ?_⟩
  rw [mul_add, hf, hf', ← map_add (f := _)]
  congr 1; ring

theorem inFr_sub {a : ZMod n} {num den : LetA O n} {f f' : W.EE} (h : InFr W a num den f)
    (h' : InFr W a num den f') : InFr W a num den (f - f') := by
  obtain ⟨u, hu, hf⟩ := h
  obtain ⟨u', hu', hf'⟩ := h'
  refine ⟨u - u', W.AΔ.sub_mem hu hu', ?_⟩
  rw [mul_sub, hf, hf', ← map_sub]
  congr 1; ring

theorem inFr_zero {a : ZMod n} {num den : LetA O n} : InFr W a num den 0 :=
  ⟨0, W.AΔ.zero_mem, by simp⟩

theorem inFr_sum {a : ZMod n} {num den : LetA O n} {ι : Type} (s : Finset ι) (F : ι → W.EE)
    (h : ∀ j ∈ s, InFr W a num den (F j)) : InFr W a num den (∑ j ∈ s, F j) := by
  induction s using Finset.induction_on with
  | empty => simpa using inFr_zero W
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact inFr_add W (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem secIn_mulA {a : ZMod n} {e d : ℕ} {cond : (ℕ → ℤ) → (Fin d → O) → Prop} {F : Fin d → W.EE}
    (h : SecIn W a e cond F) {c : LetA O n} (hc : c ∈ W.AΔ) :
    SecIn W a e cond (fun k => algebraMap (LetA O n) W.EE c * F k) := by
  obtain ⟨I, g, c₀, α, hg, hF⟩ := h
  refine ⟨I, fun i => algebraMap (LetA O n) W.EE c * g i, c₀, α, fun i => ⟨inFr_mulA W (hg i).1 hc, (hg i).2⟩,
    fun k => ?_⟩
  show algebraMap (LetA O n) W.EE c * F k = _
  rw [hF k, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dvO_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T (e + 1) b c₀ = Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V) (dvO W T e b c₀) := by
  unfold dvO dv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, pow_succ', Module.End.mul_apply]

theorem dvO_add (T : LocLat G Qp LL O) (e s : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T (e + s) b c₀ = ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ s) (dvO W T e b c₀) := by
  induction s with
  | zero => simp
  | succ s ih => rw [← add_assoc, dvO_succ, ih, pow_succ', Module.End.mul_apply]

theorem filS_succ (T : LocLat G Qp LL O) (a : ZMod n) (t : ℕ) (u : ℤ) :
    FilS W T (a + 1) (t + 1) u = (FilS W T a t u).map (Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) := by
  unfold FilS
  rw [show a + 1 - ((t + 1 : ℕ) : ZMod n) = a - (t : ZMod n) by push_cast; ring, ← Submodule.map_comp]
  congr 1
  rw [pow_succ', Module.End.mul_eq_comp]

variable [IsDomain O]

theorem secIn_transport (T : LocLat G Qp LL O) (a : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (H : ℕ) {v : LetA O n} (hv : v ∈ W.AΔ) (hπ : W.π₀ ∈ W.AΔ)
    (hlow : ∀ c₀ : Fin d → O, dvO W T (e + 1) b c₀ ∈ FilS W T (a + 1) 0 (-(H : ℤ))) (F : Fin d → W.EE)
    (hF : SecIn W a e (condNN W T a e b) F) :
    SecIn W (a + 1) (e + 1) (condNN W T (a + 1) (e + 1) b)
      (fun k => algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (F k)) := by
  obtain ⟨I, g, c₀, α, hg, hFe⟩ := hF
  refine ⟨I, fun i => algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (g i), c₀,
    fun i s => if s = 0 then (H : ℤ) else α i (s - 1), fun i => ⟨?_, ?_⟩, fun k => ?_⟩
  · obtain ⟨u, hu, hgu⟩ := (hg i).1
    refine ⟨v * W.φA u, W.AΔ.mul_mem hv (Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ hu), ?_⟩
    have hl : W.φA (letE a : LetA O n) = letE (a + 1) := by
      have := φA_letE W (a + 1); rwa [show a + 1 - 1 = a by ring] at this
    have h1 := congrArg W.φE hgu
    rw [map_mul, φE_alg, φE_alg, map_mul W.φA, map_mul W.φA, hl] at h1
    have hnum : W.φA (∏ s ∈ Finset.range e, ps W s ^ (α i s).toNat) =
        ∏ s ∈ Finset.range e, ps W (s + 1) ^ (α i s).toNat := by
      rw [map_prod]; exact Finset.prod_congr rfl fun s _ => by rw [map_pow, ← ps_succ]
    have hden : W.φA (∏ s ∈ Finset.range e, ps W s ^ (-(α i s)).toNat) =
        ∏ s ∈ Finset.range e, ps W (s + 1) ^ (-(α i s)).toNat := by
      rw [map_prod]; exact Finset.prod_congr rfl fun s _ => by rw [map_pow, ← ps_succ]
    rw [hnum, hden] at h1
    show algebraMap (LetA O n) W.EE (∏ s ∈ Finset.range (e + 1), ps W s ^
        (-(if s = 0 then (H : ℤ) else α i (s - 1))).toNat) *
        (algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (g i)) =
      algebraMap (LetA O n) W.EE ((letE (a + 1) * ∏ s ∈ Finset.range (e + 1), ps W s ^
        (if s = 0 then (H : ℤ) else α i (s - 1)).toNat) * (v * W.φA u))
    rw [Finset.prod_range_succ', Finset.prod_range_succ']
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Int.toNat_natCast,
      Int.toNat_eq_zero.2 (by omega : -(H : ℤ) ≤ 0), pow_zero, mul_one]
    rw [mul_left_comm, h1]
    simp only [map_mul]
    ring
  · intro s hs
    rcases s with _ | t
    · beta_reduce
      simp only [↓reduceIte]
      exact hlow (c₀ i)
    · beta_reduce
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [filS_succ, dvO_succ]
      exact Submodule.mem_map_of_mem ((hg i).2 t (by omega))
  · show algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (F k) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hFe k, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul W.φE, AlgHom.commutes]
    ring

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SecondLiftOfHypotheses
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem second_lift_of_hypotheses [NeZero n] (W : LocWach PD LL O v n) (hZ : TTool2Z W)
    (hF : Formalism.MainNotions.CrystallineLiftingInputs.FTool W) (hB : Sh.BasTool W) (hK : Sh.LemK W) (hD : Sh.FilDim W)
    (hR : Sh.ExpRing W) (hE : Sh.ExpRules W)
    (h2a : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p2aK W T)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hEx : DcrisExactStrict PD LL)
    (hCs : CrysSubQuot PD LL) (hDq : DdREqDcris PD LL) : Step2 W := by
  intro d T₁ T₂ F b S η m hS
  obtain ⟨hDom, hDVR, hFr⟩ := hS.2.2.2.1
  refine ⟨2 * sigC PD.p (hpar n b S) η, Step2A.sigma_bound_le _ _ _ hS.2.1, ?_⟩
  intro s₁ FF _ _ _ _ g N y z μ ν hX F₁ ms hO
  exact second_lift_at_situation W hZ hF hB hK hD hR hE h2a h5 h9 hEx hCs hDq hS s₁ g N y z μ ν hX F₁ ms hO

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

