module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.POrthZero
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.OZ

private def bump (s : ℝ) : ℂ := ((max 0 (min 1 (2 - |s|)) : ℝ) : ℂ)

private theorem bump_cont : Continuous bump := by
  unfold bump
  fun_prop

private theorem bump_supp : HasCompactSupport bump := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun s hs => ?_
  have h : 2 < |s| := by
    by_contra hc
    exact hs (abs_le.1 (not_lt.1 hc))
  have h1 : min 1 (2 - |s|) ≤ 0 := (min_le_right _ _).trans (by linarith)
  simp [bump, max_eq_left h1]

private theorem bump_one {s : ℝ} (h : s ∈ Set.Ioo (-1 : ℝ) 1) : bump s = 1 := by
  have h1 : |s| < 1 := abs_lt.2 h
  have h2 : min 1 (2 - |s|) = 1 := min_eq_left (by linarith)
  simp [bump, h2]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.OZ

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.OZ in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.orthZero_pf :
    Basic → AeEq → WtInd → OrthZero := by
  intro hB hA _ E _ _ _ n hn D π _ f hf hS ho
  obtain ⟨hl, hmul, -⟩ := hB E n hn
  obtain ⟨hfc, hfr, hfs, -⟩ := hf
  obtain ⟨v, hv, hve⟩ := hS bump bump_cont bump_supp
  have horth : v ∈ (piSp D π Unit)ᗮ := by
    rw [piSp, Submodule.orthogonal_closure, Submodule.mem_orthogonal]
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨ψ, hψ, u, hu, hus, he⟩ := hg ()
      have hz := ho ψ hψ (fun s => starRingEnd ℂ (u s) * bump s)
        ((Complex.continuous_conj.comp hu).mul bump_cont)
        ((hus.comp_left (g := starRingEnd ℂ) (map_zero _)).mul_right)
      rw [PiLp.inner_apply]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [L2.inner_def]
      rw [← hz, prW]
      refine integral_congr_ae ?_
      filter_upwards [he, hve] with x h1 h2
      simp only [PUnit.default_eq_unit]
      rw [h1, h2]
      simp only [RCLike.inner_apply, map_mul]
      ring
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul r x _ hx => rw [inner_smul_left, hx, mul_zero]
  have hv0 : v = 0 := inner_self_eq_zero.1
    ((Submodule.mem_orthogonal _ _).1 horth v hv)
  have hlat : ∀ x : H E n 0, ldet x ∈ Set.Ioo (-1 : ℝ) 1 → f x.1 = 0 := by
    refine hA E n D (fun x => f x.1) (fun _ => 0) (Set.Ioo (-1 : ℝ) 1) (hfc.comp continuous_fst)
      continuous_const ?_ (fun _ _ => rfl) isOpen_Ioo ?_
    · intro γ x
      obtain ⟨⟨a, b⟩, hab⟩ := γ.2
      have h1 : (γ : H E n 0).1 = ratGL E n a := by rw [← hab]; rfl
      show f ((γ : H E n 0).1 * x.1) = f x.1
      rw [h1, hfr]
    · have hz : ((v () : Lp ℂ 2 D.ν) : H E n 0 → ℂ) =ᵐ[D.ν] 0 := by
        rw [hv0]
        exact Lp.coeFn_zero _ _ _
      filter_upwards [hve, hz] with x h1 h2 h3
      rw [h2] at h1
      simpa [bump_one h3] using h1.symm
  funext g
  have hx := hlat (ac E n (-ldet ((g, 1) : H E n 0)) * (g, 1)) (by
    rw [hmul, hl]; simp)
  have : (ac E n (-ldet ((g, 1) : H E n 0)) * (g, 1) : H E n 0).1 =
      splitCentre E n (-ldet ((g, 1) : H E n 0) / (n * Module.finrank ℚ E)) * g := rfl
  rw [this, hfs] at hx
  exact hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPfHecke
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PfH

open scoped Pointwise

section Abs

variable {G ι : Type} [Group G] {A : ι → Type} [∀ i, Group (A i)]

private def boxes (j : ∀ i, A i →* G) (C : ∀ i, Set (A i)) : List ι → Set G
  | [] => {1}
  | i :: l => (j i '' C i) * boxes j C l

private def pr (j : ∀ i, A i →* G) (q : ∀ i, G →* A i) (x : G) (l : List ι) : G :=
  (l.map fun i => j i (q i x)).prod

private theorem boxes_compact [TopologicalSpace G] [ContinuousMul G] [∀ i, TopologicalSpace (A i)]
    (j : ∀ i, A i →* G) (C : ∀ i, Set (A i)) (hj : ∀ i, Continuous (j i)) (l : List ι)
    (h : ∀ i ∈ l, IsCompact (C i)) : IsCompact (boxes j C l) := by
  induction l with
  | nil => exact isCompact_singleton
  | cons i l ih =>
    exact ((h i (by simp)).image (hj i)).mul (ih fun k hk => h k (by simp [hk]))

private theorem pr_mem (j : ∀ i, A i →* G) (q : ∀ i, G →* A i) (C : ∀ i, Set (A i)) (x : G) (l : List ι)
    (h : ∀ i ∈ l, q i x ∈ C i) : pr j q x l ∈ boxes j C l := by
  induction l with
  | nil => simp [pr, boxes]
  | cons i l ih =>
    have h1 : j i (q i x) ∈ j i '' C i := ⟨_, h i (by simp), rfl⟩
    have h2 := ih fun k hk => h k (by simp [hk])
    simpa [pr, boxes] using Set.mul_mem_mul h1 h2

private theorem q_pr_out (j : ∀ i, A i →* G) (q : ∀ i, G →* A i) (P : ι → Prop)
    (hind : ∀ i k, P i → P k → i ≠ k → ∀ a, q k (j i a) = 1) (x : G) (k : ι) (hk : P k) (l : List ι)
    (hl : ∀ i ∈ l, P i) (hkl : k ∉ l) : q k (pr j q x l) = 1 := by
  induction l with
  | nil => simp [pr]
  | cons i l ih =>
    have hne : i ≠ k := fun e => hkl (by simp [e])
    have h2 : q k (pr j q x l) = 1 :=
      ih (fun m hm => hl m (by simp [hm])) (fun hm => hkl (by simp [hm]))
    have h3 : pr j q x (i :: l) = j i (q i x) * pr j q x l := by simp [pr]
    rw [h3, map_mul, h2, hind i k (hl i (by simp)) hk hne, one_mul]

private theorem q_pr_in (j : ∀ i, A i →* G) (q : ∀ i, G →* A i) (P : ι → Prop)
    (hjq : ∀ i a, q i (j i a) = a)
    (hind : ∀ i k, P i → P k → i ≠ k → ∀ a, q k (j i a) = 1) (x : G) (k : ι) (l : List ι)
    (hl : ∀ i ∈ l, P i) (hnd : l.Nodup) (hkl : k ∈ l) : q k (pr j q x l) = q k x := by
  induction l with
  | nil => simp at hkl
  | cons i l ih =>
    have h3 : pr j q x (i :: l) = j i (q i x) * pr j q x l := by simp [pr]
    have hl' : ∀ m ∈ l, P m := fun m hm => hl m (by simp [hm])
    obtain ⟨hi, hnd'⟩ := List.nodup_cons.1 hnd
    by_cases e : k = i
    · subst e
      rw [h3, map_mul, hjq, q_pr_out j q P hind x k (hl k (by simp)) l hl' hi, mul_one]
    · have hk' : k ∈ l := by simpa [e] using hkl
      rw [h3, map_mul, ih hl' hnd' hk', hind i k (hl i (by simp)) (hl k (by simp [hk'])) (Ne.symm e), one_mul]

private theorem abs_support [TopologicalSpace G] [IsTopologicalGroup G] [∀ i, TopologicalSpace (A i)]
    (j : ∀ i, A i →* G) (q : ∀ i, G →* A i) (hj : ∀ i, Continuous (j i)) (P : ι → Prop)
    (N : ∀ i, Subgroup (A i)) (L : Subgroup G) (hL : ∀ x, x ∈ L ↔ ∀ i, P i → q i x ∈ N i)
    (hLo : IsOpen (L : Set G)) (hLc : IsCompact (L : Set G)) (hjq : ∀ i a, q i (j i a) = a)
    (hind : ∀ i k, P i → P k → i ≠ k → ∀ a, q k (j i a) = 1) (I : Finset ι) (hI : ∀ i ∈ I, P i)
    (C : ∀ i, Set (A i)) (hC : ∀ i ∈ I, IsCompact (C i)) (f : G → ℂ)
    (hinv : ∀ k ∈ L, ∀ x, f (x * k) = f x)
    (hs : ∀ x, f x ≠ 0 → (∀ i ∈ I, q i x ∈ C i) ∧ ∀ i, P i → i ∉ I → q i x ∈ N i) :
    HasCompactSupport f := by
  classical
  have hcl : IsClosed (Function.support f) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hx0 : f x = 0 := by simpa using hx
    have hop : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (L : Set G)) :=
      hLo.preimage (continuous_const.mul continuous_id)
    have hmem : x ∈ (fun y => x⁻¹ * y) ⁻¹' (L : Set G) := by simp [L.one_mem]
    refine Filter.mem_of_superset (hop.mem_nhds hmem) ?_
    intro y hy
    have : f (x * (x⁻¹ * y)) = f x := hinv _ hy x
    simpa [hx0] using this
  have hl : ∀ i ∈ I.toList, P i := fun i hi => hI i (by simpa using hi)
  have hK : IsCompact (boxes j C I.toList * (L : Set G)) :=
    (boxes_compact j C hj _ fun i hi => hC i (by simpa using hi)).mul hLc
  have hsub : Function.support f ⊆ boxes j C I.toList * (L : Set G) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hs x hx
    have hb := pr_mem j q C x I.toList fun i hi => h1 i (by simpa using hi)
    have hy : (pr j q x I.toList)⁻¹ * x ∈ L := by
      refine (hL _).2 fun k hk => ?_
      by_cases hkI : k ∈ I
      · rw [map_mul, map_inv, q_pr_in j q P hjq hind x k _ hl I.nodup_toList (by simpa using hkI)]
        simp [(N k).one_mem]
      · rw [map_mul, map_inv, q_pr_out j q P hind x k hk _ hl (by simpa using hkI)]
        simpa using h2 k hk hkI
    have := Set.mul_mem_mul hb hy
    simpa using this
  show IsCompact (closure (Function.support f))
  rw [hcl.closure_eq]
  exact hK.of_isClosed_subset hcl hsub

end Abs

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PfH

open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun in
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PfH in
open scoped Classical in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pfHecke_pf :
    SlotBasic → LevTop → PfHecke := by
  intro hSF hLT E _ _ _ n S Z N hS hZ hN I F hF
  obtain ⟨-, -, hloc, hind, hfinK, -, -⟩ := hSF E n S hS
  obtain ⟨hLo, hLc, -, -⟩ := hLT E n S Z N hS hZ hN
  have hLev : ∀ x, x ∈ Lev S N ↔ ∀ i : Pl E × Bool, Sl S i → qw n i.1 i.2 x ∈ N i.1 := by
    intro x
    simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]

  have hposition : ∀ i : Pl E × Bool, Sl S i → ∀ a ∈ N i.1, ∀ x,
      F i.1 i.2 (a * x) = F i.1 i.2 x ∧ F i.1 i.2 (x * a) = F i.1 i.2 x := by
    intro i hi a ha x
    by_cases hiI : i ∈ I
    · exact (hF.1 i hiI).2.2 a ha x
    · rw [hF.2 i hi hiI]
      constructor
      · by_cases hx : x ∈ N i.1
        · rw [Set.indicator_of_mem (show a * x ∈ (N i.1 : Set _) from (N i.1).mul_mem ha hx),
            Set.indicator_of_mem (show x ∈ (N i.1 : Set _) from hx)]
          rfl
        · rw [Set.indicator_of_notMem (show a * x ∉ (N i.1 : Set _) from
              fun h => hx ((Subgroup.mul_mem_cancel_left _ ha).1 h)),
            Set.indicator_of_notMem (show x ∉ (N i.1 : Set _) from hx)]
      · by_cases hx : x ∈ N i.1
        · rw [Set.indicator_of_mem (show x * a ∈ (N i.1 : Set _) from (N i.1).mul_mem hx ha),
            Set.indicator_of_mem (show x ∈ (N i.1 : Set _) from hx)]
          rfl
        · rw [Set.indicator_of_notMem (show x * a ∉ (N i.1 : Set _) from
              fun h => hx ((Subgroup.mul_mem_cancel_right _ ha).1 h)),
            Set.indicator_of_notMem (show x ∉ (N i.1 : Set _) from hx)]

  have hfalse : ∀ w, w ∈ S → Sl S (w, false) := fun w hw => ⟨hw, by simp⟩
  have htrue : ∀ w, w ∈ S → IsSplitAt w → Sl S (w, true) := fun w hw hs => ⟨hw, fun _ => hs⟩
  have hinvL : ∀ k ∈ Lev S N, ∀ x, pf S F (k * x) = pf S F x := by
    intro k hk x
    refine finprod_congr fun w => finprod_congr fun hw => ?_
    have hk' := (hLev k).1 hk
    have h1 := (hposition (w, false) (hfalse w hw) _ (hk' _ (hfalse w hw)) (qw n w false x)).1
    simp only [map_mul] at h1 ⊢
    rw [h1]
    by_cases hs : IsSplitAt w
    · have h2 := (hposition (w, true) (htrue w hw hs) _ (hk' _ (htrue w hw hs)) (qw n w true x)).1
      simp only [if_pos hs]
      rw [h2]
    · simp only [if_neg hs]
  have hinvR : ∀ k ∈ Lev S N, ∀ x, pf S F (x * k) = pf S F x := by
    intro k hk x
    refine finprod_congr fun w => finprod_congr fun hw => ?_
    have hk' := (hLev k).1 hk
    have h1 := (hposition (w, false) (hfalse w hw) _ (hk' _ (hfalse w hw)) (qw n w false x)).2
    simp only [map_mul] at h1 ⊢
    rw [h1]
    by_cases hs : IsSplitAt w
    · have h2 := (hposition (w, true) (htrue w hw hs) _ (hk' _ (htrue w hw hs)) (qw n w true x)).2
      simp only [if_pos hs]
      rw [h2]
    · simp only [if_neg hs]

  have hfac : ∀ x : GF E n, pf S F x ≠ 0 → ∀ w ∈ S,
      (F w false (qw n w false x) * if IsSplitAt w then F w true (qw n w true x) else 1) ≠ 0 := by
    intro x hx w hw h0
    apply hx
    classical
    set fac : Pl E → ℂ := fun w =>
      F w false (qw n w false x) * if IsSplitAt w then F w true (qw n w true x) else 1 with hfacdef
    have hbad := hfinK x
    have hfin : (S ∩ Function.mulSupport fac).Finite := by
      refine ((Z.finite_toSet.union (I.image Prod.fst).finite_toSet).union
        (hbad.image Prod.fst)).subset ?_
      rintro u ⟨hu, hne⟩
      by_contra hout
      simp only [Set.mem_union, Finset.mem_coe, Finset.mem_image, Set.mem_image, Set.mem_setOf_eq,
        not_or, not_exists, not_and] at hout
      obtain ⟨⟨huZ, huI⟩, hub⟩ := hout
      have hNu : N u = KGL u n := (hN u).2.2.2 huZ
      have hone : ∀ b, Sl S (u, b) → F u b (qw n u b x) = 1 := by
        intro b hb
        have hnotI : (u, b) ∉ I := fun h => huI (u, b) h rfl
        have hq : qw n u b x ∈ KGL u n := by
          by_contra hq
          exact hub (u, b) hq rfl
        rw [hF.2 (u, b) hb hnotI]
        simp only
        rw [hNu, Set.indicator_of_mem (show qw n u b x ∈ (KGL u n : Set _) from hq)]
        rfl
      apply hne
      simp only [hfacdef]
      rw [hone false (hfalse u hu)]
      by_cases hs : IsSplitAt u
      · simp only [if_pos hs]
        rw [hone true (htrue u hu hs), one_mul]
      · simp only [if_neg hs, one_mul]
    have hwm : w ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      refine ⟨hw, ?_⟩
      show fac w ≠ 1
      rw [show fac w = 0 from h0]
      exact zero_ne_one
    show (∏ᶠ w ∈ S, fac w) = 0
    rw [finprod_mem_eq_prod fac hfin]
    exact Finset.prod_eq_zero hwm h0

  have hval : ∀ x : GF E n, pf S F x ≠ 0 → ∀ i : Pl E × Bool, Sl S i → F i.1 i.2 (qw n i.1 i.2 x) ≠ 0 := by
    rintro x hx ⟨w, b⟩ ⟨hw, hb⟩
    have h := hfac x hx w hw
    cases b with
    | false => exact left_ne_zero_of_mul h
    | true =>
      have hs := hb rfl
      have h2 := right_ne_zero_of_mul h
      rwa [if_pos hs] at h2
  refine ⟨?_, fun k hk x => ⟨hinvL k hk x, hinvR k hk x⟩⟩
  refine abs_support (ι := Pl E × Bool) (A := fun i => GLw n i.1)
    (fun i => jw n i.1 i.2) (fun i => qw n i.1 i.2) (fun i => (hloc i.1 i.2).1) (Sl S)
    (fun i => N i.1) (Lev S N) hLev hLo hLc (fun i a => (hloc i.1 i.2).2.2.1 a)
    (fun i k hi hk hne a => hind i k hi hk hne a) I (fun i hi => (hF.1 i hi).1)
    (fun i => tsupport (F i.1 i.2)) (fun i hi => (hF.1 i hi).2.1) (pf S F) hinvR ?_
  intro x hx
  refine ⟨fun i hi => subset_tsupport _ (hval x hx i (hF.1 i hi).1), fun i hi hiI => ?_⟩
  have h := hval x hx i hi
  rw [hF.2 i hi hiI] at h
  by_contra hq
  exact h (Set.indicator_of_notMem hq _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPiTermOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelG borelF borelA borelH

private theorem lev_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (S : Set (Pl E))
    {N N' : ∀ w : Pl E, Subgroup (GLw n w)} (h : ∀ w, N w ≤ N' w) : Lev S N ≤ Lev S N' := by
  intro g hg
  simp only [Lev, Subgroup.mem_iInf] at hg ⊢
  exact fun i => h _ (hg i)

private theorem level_term (h1 : ThetaFixedGlobalWeights) (h3 : LevTop) (h6 : ToYd) (h7 : LevelTr)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 1 ≤ n) (π : CuspSub E n)
    (hreg : (CG.mk π).IsRegAlg) (hd : GlobalTheory.ContraPair.DualIsConj π) (lamE : (E →+* ℂ) → DomWeight n)
    (hlam : ∀ φ, π.HasInfChar φ (infOfWeight (lamE φ))) {S : Set (Pl E)} (hS : IsSection S)
    {Z : Finset (Pl E)} (hZ : SplitIn S Z) {B : Pl E → Multiset ℂˣ} {τ : ∀ w : Pl E, SmIrr (GLw n w)}
    (hB : ∀ w, Off Z w → (CG.mk π).HasSat w (B w)) (hτ : ∀ w ∈ Z, π.IsLocComp w (τ w))
    {u : GL (Fin n) E} (hu : IsTransl u) (μC : Measure (G n)) (μ : Measure (H E n 0))
    [μC.IsHaarMeasure] [μ.IsHaarMeasure] {N : ∀ w : Pl E, Subgroup (GLw n w)} (hN : Good Z N)
    (hfix : ∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ Lev S N, finRep E n k ψ = ψ) :
    (∃ φ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ N' ≤ N w, ∀ b, IsHecke N' (two φ φ w b)) ∧
      (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ φ w (g, 1)) ≠ 0) ∧
    ∃ c : ℂ, c ≠ 0 ∧ ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) →
      ∀ T : Finset (Pl E), Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1)))
        (k : ∀ v : InfinitePlace E, Mat n → ((lefE n (lamE v.embedding).w).V →L[ℂ] (lefE n (lamE v.embedding).w).V))
        (vl : InfinitePlace E → Inf n → ℂ) (R : ℝ),
        TEv S T e₂ → (∀ v : InfinitePlace E, IsMult μC (lefE n (lamE v.embedding).w) (k v) (vl v) R) →
        IsTwTr μ π (phiProd (fun v => (lamE v.embedding).w) k (finU S u (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)))
          (c * (∏ v : InfinitePlace E, vl v (infOf (lamE v.embedding).w)) *
            (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0) := by
  obtain ⟨hKo, hKc, -, -⟩ := h3 E n S Z N hS hZ hN
  obtain ⟨hKθ, hY⟩ := h6 E n S Z N hS hZ hN π u hu
  let K₀ : TopologicalSpace.PositiveCompacts (GF E n) :=
    ⟨⟨(Lev S N : Set (GF E n)), hKc⟩, by
      show (interior (Lev S N : Set (GF E n))).Nonempty
      rw [hKo.interior_eq]
      exact ⟨1, (Lev S N).one_mem⟩⟩
  let μf : Measure (GF E n) := Measure.haarMeasure K₀
  haveI : μf.IsHaarMeasure := inferInstance
  obtain ⟨Y, ρ, A, cK, hYπ, hfd, hne, hYfix, hact, hsimple, hsq, htw, hcK, htr⟩ :=
    h1 E n hn π hreg hd lamE hlam (Lev S N) hKo hKc hKθ hfix μC μf μ
  obtain ⟨y, v, hv, hyv⟩ := hY μf inferInstance Y ρ A hYπ hfd hne hYfix hact hsimple hsq htw
  obtain ⟨href, d, hd0, hdtr⟩ := h7 E n S Z N hS hZ hN π y B τ hB hτ
  refine ⟨href, cK * v * d, mul_ne_zero (mul_ne_zero hcK hv) hd0, ?_⟩
  intro φ₁ φ₂ hφ T hT e₁ e₂ k vl R hE hM
  obtain ⟨hH, hTr⟩ := hdtr φ₁ φ₂ hφ T hT e₁ e₂ hE
  obtain ⟨hHF, hTrY⟩ := hyv _ hH
  have key := htr k vl (fun _ => R) hM _ hHF
  rw [hTrY, hTr] at key
  have e : cK * (∏ w : InfinitePlace E, vl w (infOf (lamE w.embedding).w)) *
      (v * (d * (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0)) =
      cK * v * d * (∏ v : InfinitePlace E, vl v (infOf (lamE v.embedding).w)) *
        (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0 := by ring
  rw [e] at key
  exact key

theorem piTerm_of_weights_levels :
    ThetaFixedGlobalWeights → WtEx → LevTop → LevFix → LcLevel → ToYd → LevelTr → TwUniq → PiTerm := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 E _ _ _ _ n hn π hreg hd
  obtain ⟨lamE, hlam⟩ := h2 E n π hreg
  refine ⟨fun v => lamE v.embedding, fun v => hlam _, ?_⟩
  intro S hS Z hZ B τ hB hτ u hu μC μ _ _
  obtain ⟨N₀, hN₀, ψ, hψ, hψ0, hψfix⟩ := h4 E n π S Z hS hZ fun w hw => ⟨B w, hB w hw⟩
  obtain ⟨⟨φr, hr, hrne⟩, c₀, hc₀, hlev₀⟩ := level_term h1 h3 h6 h7 hn π hreg hd lamE hlam hS hZ hB hτ hu μC μ hN₀
    ⟨ψ, hψ, hψ0, hψfix⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro φ₁ φ₂ hφ T hT e₁ e₂ k vl R hE hM
  obtain ⟨N, hN, hle, hHecke⟩ := h5 E n Z N₀ hN₀ φ₁ φ₂ hφ
  obtain ⟨-, c, -, hlev⟩ := level_term h1 h3 h6 h7 hn π hreg hd lamE hlam hS hZ hB hτ hu μC μ hN
    ⟨ψ, hψ, hψ0, fun g hg => hψfix g (lev_mono S hle hg)⟩
  have main := hlev φ₁ φ₂ hHecke T hT e₁ e₂ k vl R hE hM
  by_cases hP : (∏ v : InfinitePlace E, vl v (infOf (lamE v.embedding).w)) = 0
  · rw [hP] at main ⊢
    simpa using main

  have hcc : c = c₀ := by
    let e : Pl E → Ex (Fin (n + 1) × Fin (0 + 1)) := fun _ => Ex.one
    have hEe : TEv S (∅ : Finset (Pl E)) e := ⟨by simp, by simp⟩
    have a₀ := hlev₀ φr φr (fun w hw b => hr w hw (N₀ w) le_rfl b) ∅ (Finset.disjoint_empty_left Z) e e k vl R hEe hM
    have a₁ := hlev φr φr (fun w hw b => hr w hw (N w) (hle w) b) ∅ (Finset.disjoint_empty_left Z) e e k vl R hEe hM
    have heq := h8 E n μ π _ _ _ a₁ a₀
    simp only [val, Finset.prod_empty, mul_one] at heq
    exact mul_right_cancel₀ hP (mul_right_cancel₀ hrne heq)
  rw [hcc] at main
  exact main

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.YLocPf
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.yLoc_pf :
    PfHecke → ProdOp → YLoc := by
  intro hP hO E _ _ _ n S Z N hS hZ hG π y i hi f hf x hx
  classical
  obtain ⟨w, b⟩ := i
  let F : ∀ w', Bool → _ := fun w' b' =>
    if h : w' = w ∧ b' = b then h.1 ▸ f else ((N w' : Set _).indicator 1)
  have hFi : F w b = f := by simp [F]
  have hFam : Fam S N {(w, b)} F := by
    refine ⟨?_, ?_⟩
    · intro j hj
      obtain rfl := Finset.mem_singleton.mp hj
      exact ⟨hi, by simpa [hFi] using hf⟩
    · rintro ⟨w', b'⟩ _ hj
      have hne : ¬ (w' = w ∧ b' = b) := by
        rintro ⟨rfl, rfl⟩
        exact hj (Finset.mem_singleton_self _)
      simp [F, hne]
  have h1 := hO E n S Z N hS hZ hG {(w, b)} F hFam x (y.fix hx)
  have h2 := y.act _ (hP E n S Z N hS hZ hG {(w, b)} F hFam) ⟨x, hx⟩
  have h3 : Lw N w b f x = ((y.r (pf S F) ⟨x, hx⟩ : y.Y) : _) := by
    rw [h2]
    show _ = Lv _ _ _ x
    rw [h1]
    simp [hFi]
  show Lw N w b f x ∈ y.Y
  rw [h3]
  exact (y.r (pf S F) ⟨x, hx⟩).2
end

