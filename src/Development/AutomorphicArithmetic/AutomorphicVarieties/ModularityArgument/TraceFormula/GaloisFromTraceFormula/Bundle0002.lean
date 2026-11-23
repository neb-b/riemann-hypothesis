module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0336

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.EndoS
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.endoS :
    Enlarge → Places → EndoBlockG → EndoBlockS := by
  intro hEn hP hG E _ _ _ hunr a b hab S hS l₁ l₂ Z hZ φ hφ hreg
  obtain ⟨J, _, D₁, D₂, B₁, B₂, hSat, hInf, hGr⟩ := hG E hunr a b hab S hS l₁ l₂ Z hZ φ hφ hreg
  have hoff : ∀ w : Pl E, ¬ IsSplitAt w → Off Z w := fun w hw => by
    have hc : cPl w = w := by
      by_contra h
      exact hw (((hP E).2.1 w).2.2 h)
    have hz : w ∉ Z := fun h => hw (hZ w h).2
    exact ⟨hz, by rw [hc]; exact hz⟩
  let St : J → Prop := fun j =>
    ∀ w : Pl E, ¬ IsSplitAt w → inv (B₁ j w) = B₁ j w ∧ inv (B₂ j w) = B₂ j w
  have hu : ∀ i : {j // ¬ St j}, ∃ w : Pl E, ¬ IsSplitAt w ∧
      ¬ (inv (B₁ i.1 w) = B₁ i.1 w ∧ inv (B₂ i.1 w) = B₂ i.1 w) := fun i => by
    by_contra h
    exact i.2 fun w hw => by_contra fun h' => h ⟨w, hw, h'⟩
  choose u hu₁ hu₂ using hu
  classical
  refine ⟨{j // St j}, inferInstance, fun j => D₁ j.1, fun j => D₂ j.1, fun j => B₁ j.1, fun j => B₂ j.1,
    fun j w h => hSat j.1 w h, fun j => hInf j.1, fun j w h => j.2 w h, ?_⟩
  intro T hT hTZ e₁ e₂ ρ hρ hlt
  obtain ⟨T', e₁', e₂', hT'S, hT'Z, hone, hzero, hval, hgeom⟩ :=
    hEn E hunr a b S hS Z T hZ hT hTZ e₁ e₂ {j // ¬ St j} u (fun i => B₁ i.1) (fun i => B₂ i.1) fun i =>
      ⟨hu₁ i, sat_card (hSat i.1 (u i) (hoff _ (hu₁ i))).1, sat_card (hSat i.1 (u i) (hoff _ (hu₁ i))).2, hu₂ i⟩
  have hsm := hGr T' hT'S hT'Z e₁' e₂' ρ hone hρ fun j => by
    by_cases hj : St j
    · rw [hval (B₁ j) (B₂ j) fun i =>
        ⟨sat_card (hSat j (u i) (hoff _ (hu₁ i))).1, sat_card (hSat j (u i) (hoff _ (hu₁ i))).2,
          (hj (u i) (hu₁ i)).1, (hj (u i) (hu₁ i)).2⟩]
      exact hlt ⟨j, hj⟩
    · have h0 := hzero ⟨j, hj⟩
      simp only at h0
      rw [h0, norm_zero]
      exact hρ
  simpa only [hgeom] using hsm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.Enlarge
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private noncomputable def listProd {ι : Type} {a b : ℕ} (d : ι → Ex (Fin (a + 1) × Fin (b + 1))) :
    List ι → Ex (Fin (a + 1) × Fin (b + 1))
  | [] => .one
  | i :: l => .mul (d i) (listProd d l)

private theorem list_prod_unitary_test {ι : Type} {a b : ℕ} {d : ι → Ex (Fin (a + 1) × Fin (b + 1))}
    (h : ∀ i, U1 (d i)) : ∀ l : List ι, U1 (listProd d l)
  | [] => .one
  | i :: l => .mul (h i) (list_prod_unitary_test h l)

private theorem listProd_ev_zero {ι : Type} {a b : ℕ} {d : ι → Ex (Fin (a + 1) × Fin (b + 1))}
    (x : Fin (a + 1) × Fin (b + 1) → ℂ) {i : ι} (h0 : (d i).ev x = 0) :
    ∀ l : List ι, i ∈ l → (listProd d l).ev x = 0
  | [], h => by simp at h
  | j :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [listProd, Ex.ev, h0]
    · simp [listProd, Ex.ev, listProd_ev_zero x h0 l h]

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula

open scoped Classical in
theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.enlarge :
    StUnit → EvaluationAtUnitaryOne → SeparatesUnitaryOne → Places → Enlarge := by
  intro hSt hEv hSep hPl E _ _ _ hunr a b S hS Z T hZ hT hTZ e₁ e₂ I _ u C₁ C₂ hC
  obtain ⟨-, hcp, -, hsec⟩ := hPl E
  have hd : ∀ i, ∃ e, U1 e ∧ ev2 a b (u i) e (C₁ i (u i)) (C₂ i (u i)) = 0 := fun i =>
    hSep E (u i) a b _ _ (hC i).2.1 (hC i).2.2.1 (hC i).2.2.2
  choose d hdU hd0 using hd
  haveI : Fintype I := Fintype.ofFinite I
  have hnsS : ∀ w : Pl E, ¬ IsSplitAt w → w ∈ S := by
    intro w hw
    have hc : cPl w = w := by
      by_contra h
      exact hw ((hcp w).2.2 h)
    rcases (hsec S hS w).1 with h | h
    · exact h
    · rwa [hc] at h
  have hTns : ∀ w ∈ T, IsSplitAt w := fun w hw => (hT w hw).2
  have hZns : ∀ w ∈ Z, IsSplitAt w := fun w hw => (hZ w hw).2
  let L : Pl E → List I := fun w => (Finset.univ.filter fun i => u i = w).toList
  let T' : Finset (Pl E) := T ∪ Finset.univ.image u
  let f₁ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)) := fun w => if w ∈ T then e₁ w else listProd d (L w)
  let f₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)) := fun w => if w ∈ T then e₂ w else .one
  have hfU : ∀ w, w ∉ T → U1 (f₁ w) := by
    intro w hw
    simp only [f₁, if_neg hw]
    exact list_prod_unitary_test hdU _
  have hf₂ : ∀ w, w ∉ T → f₂ w = .one := fun w hw => by simp only [f₂, if_neg hw]
  have hT'ns : ∀ w ∈ T', w ∉ T → ¬ IsSplitAt w := by
    intro w hw hwT
    rcases Finset.mem_union.1 hw with h | h
    · exact absurd h hwT
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact (hC i).1
  have huT : ∀ i, u i ∉ T := fun i h => (hC i).1 (hTns _ h)
  refine ⟨T', f₁, f₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    by_cases hwT : w ∈ T
    · exact (hT w hwT).1
    · exact hnsS w (hT'ns w hw hwT)
  · rw [Finset.disjoint_left]
    intro w hw hwZ
    by_cases hwT : w ∈ T
    · exact Finset.disjoint_left.1 hTZ hwT hwZ
    · exact hT'ns w hw hwT (hZns w hwZ)
  · intro w hw hns
    have hwT : w ∉ T := fun h => hns (hTns w h)
    exact hf₂ w hwT
  · intro i
    refine Finset.prod_eq_zero (i := u i) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))) ?_
    have : ev2 a b (u i) (f₁ (u i)) (C₁ i (u i)) (C₂ i (u i)) = 0 := by
      simp only [f₁, if_neg (huT i)]
      refine listProd_ev_zero _ (hd0 i) _ ?_
      simp [L]
    rw [this, zero_mul]
  · intro B₁ B₂ hB
    unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.val
    symm
    have hsub : T ⊆ T' := Finset.subset_union_left
    rw [← Finset.prod_subset hsub]
    · refine Finset.prod_congr rfl fun w hw => ?_
      simp only [f₁, f₂, if_pos hw]
    · intro w hw hwT
      rcases Finset.mem_union.1 hw with h | h
      · exact absurd h hwT
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      rw [hf₂ _ hwT, hEv E (u i) a b _ (hfU _ hwT) _ _ (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2]
      simp [ev2, Ex.ev]
  · intro l₁ l₂ φ k
    have hloc : ∀ (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]), Q₁.Separable → Q₂.Separable →
        stTw2 a b w Q₁ Q₂ (fam Z T' φ f₁ f₂ k w) = stTw2 a b w Q₁ Q₂ (fam Z T φ e₁ e₂ k w) := by
      intro w Q₁ Q₂ h₁ h₂
      unfold fam
      by_cases hwZ : w ∈ Z
      · simp only [if_pos hwZ]
      simp only [if_neg hwZ]
      by_cases hwT : w ∈ T
      · have hw' : w ∈ T' := Finset.mem_union_left _ hwT
        simp only [if_pos hwT, if_pos hw', f₁, f₂]
      by_cases hw' : w ∈ T'
      · simp only [if_neg hwT, if_pos hw']
        rw [hf₂ w hwT]
        exact hSt E hunr w (hT'ns w hw' hwT) a b _
          (.mul ((hfU w hwT).pow k) ((U1.one).pow k)) Q₁ Q₂ h₁ h₂
      · simp only [if_neg hwT, if_neg hw']
    unfold PositivityTheory.Rg.BcB.G8.geomSt2
    refine finsum_mem_congr rfl fun p hp => ?_
    congr 1
    refine finprod_congr fun w => finprod_congr fun _ => ?_
    exact hloc w _ _ (hp.1.2.2.1.map) (hp.2.1.2.2.1.map)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.HeckeEigenvaluesUnitaryOneFactor
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem satEig_rev_of_stable {q n : ℕ} {B : Multiset ℂˣ} (hB : B.card = n) (hs : inv B = B)
    (i : Fin (n + 1)) : satEig q n B (i.rev : ℕ) = satEig q n B n * satEig q n B (i : ℕ) := by
  have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
  have h := GlobalTheory.LFun.ConjPlace.satEig_inv_mul (q := q) hB hi
  have hs' : B.map (·⁻¹) = B := hs
  rw [hs'] at h
  have hr : (i.rev : ℕ) = n - (i : ℕ) := by
    rw [Fin.val_rev]; omega
  rw [hr, ← h, mul_comm]

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.hecke_eigenvalues_unitary_one_factor :
    EvaluationAtUnitaryOne := by
  intro E _ _ _ w a b e he B₁ B₂ h₁ h₂ s₁ s₂
  induction he with
  | one => simp [ev2, Ex.ev]
  | step c p =>
    have r₁ := satEig_rev_of_stable (q := qV E w) h₁ s₁ p.1
    have r₂ := satEig_rev_of_stable (q := qV E w) h₂ s₂ p.2
    simp only [ev2, Ex.ev, dEx, Fin.val_last, r₁, r₂]
    ring
  | mul _ _ ih₁ ih₂ =>
    simp only [ev2, Ex.ev] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.MtoLaws
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem rel_comp {r s t : ℂ → ℂ → Prop} (h : ∀ x y z, r x y → s y z → t x z)
    {a b c : Multiset ℂ} (hab : Multiset.Rel r a b) :
    Multiset.Rel s b c → Multiset.Rel t a c := by
  induction hab generalizing c with
  | zero =>
    intro h0
    rw [Multiset.rel_zero_left] at h0
    subst h0
    exact Multiset.Rel.zero
  | cons hxy _ ih =>
    intro hc
    obtain ⟨z, zs, hz, hzs, rfl⟩ := Multiset.rel_cons_left.1 hc
    exact Multiset.Rel.cons (h _ _ _ hxy hz) (ih hzs)

private theorem exists_sep (S : Finset (ℂ × ℂ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ S, p.1 ≠ p.2 → ε < ‖p.1 - p.2‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert p S _ ih =>
    obtain ⟨ε, h0, hε⟩ := ih
    by_cases hp : p.1 = p.2
    · refine ⟨ε, h0, fun q hq hne => ?_⟩
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact absurd hp hne
      · exact hε q hq hne
    · have hpos : 0 < ‖p.1 - p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hp)
      refine ⟨min ε (‖p.1 - p.2‖ / 2), lt_min h0 (half_pos hpos), fun q hq hne => ?_⟩
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact (min_le_right _ _).trans_lt (half_lt_self hpos)
      · exact (min_le_left _ _).trans_lt (hε q hq hne)

private theorem eq_of_rel {a b : Multiset ℂ}
    (h : ∀ ε : ℝ, 0 < ε → Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) a b) : a = b := by
  classical
  obtain ⟨ε, h0, hε⟩ := exists_sep (a.toFinset ×ˢ b.toFinset)
  refine Multiset.rel_eq.1 ((h ε h0).mono fun x hx y hy hxy => ?_)
  by_contra hne
  exact absurd hxy (not_le.2 (hε (x, y) (by simp [hx, hy]) hne))

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.mtoLaws :
    MToLaws := by
  intro E _ _ _
  refine ⟨fun m x y hx hy => ?_, fun m x z z₀ hx hz τ ε hε => ?_,
    fun m m' x x' hx hx' τ ε hε => ?_⟩
  · funext τ
    refine eq_of_rel fun ε hε => ?_
    obtain ⟨k, h1, h2⟩ := ((hx τ (ε / 2) (half_pos hε)).and (hy τ (ε / 2) (half_pos hε))).exists
    refine rel_comp (fun p q w (hpq : ‖q - p‖ ≤ ε / 2) (hqw : ‖q - w‖ ≤ ε / 2) => ?_)
      (Multiset.rel_flip.2 h1) h2
    calc ‖p - w‖ = ‖(q - w) - (q - p)‖ := by congr 1; ring
      _ ≤ ‖q - w‖ + ‖q - p‖ := norm_sub_le _ _
      _ ≤ ε := by linarith
  · have hz' : ∀ᶠ k in atTop, ‖z k - z₀‖ ≤ ε / 2 :=
      (Metric.tendsto_nhds.1 hz (ε / 2) (half_pos hε)).mono fun k hk => by
        rw [dist_eq_norm] at hk
        exact hk.le
    filter_upwards [hx τ (ε / 2) (half_pos hε), hz'] with k h1 h2
    refine Multiset.rel_map.2 (h1.mono fun p _ q _ hpq => ?_)
    calc ‖(p + z k) - (q + z₀)‖ = ‖(p - q) + (z k - z₀)‖ := by congr 1; ring
      _ ≤ ‖p - q‖ + ‖z k - z₀‖ := norm_add_le _ _
      _ ≤ ε := by linarith
  · filter_upwards [hx τ ε hε, hx' τ ε hε] with k h1 h2
    exact h1.add h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.MuInf
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.muInf :
    MuInf := by
  intro E _ _ _ μ e hμ
  refine ⟨fun w hw => ?_, fun N k P v => ⟨?_, ?_⟩⟩
  · simpa using UpperTheory.HeckeLevelFrameExistence.muVal E μ e hμ w hw 1
  · rw [((ParLaws.hasInfChar_infChar P v.embedding).twist (μ ^ k)).infChar_eq]
    refine Multiset.map_congr rfl fun z _ => ?_
    rw [GlobalTheory.BCT.TwistDisc.expo_pow, GlobalTheory.BCT.MuProps.expo_emb hμ]
    ring
  · rw [((ParLaws.hasInfChar_infChar P (ComplexEmbedding.conjugate v.embedding)).twist (μ ^ k)).infChar_eq]
    refine Multiset.map_congr rfl fun z _ => ?_
    rw [GlobalTheory.BCT.TwistDisc.expo_pow, GlobalTheory.BCT.MuProps.expo_conj hμ]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.MwAt
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.mwAt :
    MWAt := by
  intro E _ _ _ n l v
  have hne : ComplexEmbedding.conjugate v.embedding ≠ v.embedding := fun h =>
    (InfinitePlace.isComplex_iff.1 (NumberField.IsTotallyComplex.isComplex v))
      (ComplexEmbedding.isReal_iff.2 h)
  have hmk : InfinitePlace.mk (ComplexEmbedding.conjugate v.embedding) = v := by
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  constructor
  · unfold mW PositivityTheory.Rg.BcB.CG.mOf infOfWeight PositivityTheory.RgBcC.infOf
    simp only [InfinitePlace.mk_embedding, decide_true, if_true, one_mul]
    congr 1
    funext k
    rw [add_sub_assoc]
  · unfold mW PositivityTheory.Rg.BcB.CG.mOf infOfWeight PositivityTheory.RgBcC.infOf
    simp only [hmk, hne, decide_false, Multiset.map_map]
    congr 1
    funext k
    simp only [Bool.false_eq_true, ite_false, Function.comp_apply]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.RegOf
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.regOf :
    MWAt → DualWt → RegOf := by
  intro mw dw E _ _ _ n l D hD τ
  have hτ := hD τ
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · refine ⟨l (InfinitePlace.mk τ), ?_⟩
    have h1 := (mw E n l (InfinitePlace.mk τ)).1
    rw [h] at h1
    rw [hτ, h1]
  · obtain ⟨lam, hlam⟩ := dw n (l (InfinitePlace.mk τ))
    refine ⟨lam, ?_⟩
    have hc : ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding = τ := by
      rw [h]
      ext x
      simp [ComplexEmbedding.conjugate_coe_eq]
    have h2 := (mw E n l (InfinitePlace.mk τ)).2
    rw [hc] at h2
    rw [hτ, h2, hlam]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.SeparatesUnitaryOne
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem inv_eq_of_eig {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) {n : ℕ}
    {B : Multiset ℂˣ} (hB : B.card = n)
    (h : ∀ i ≤ n, satEig (qV E w) n B n * satEig (qV E w) n B i = satEig (qV E w) n B (n - i)) :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.inv B = B := by
  have hne : satEig (qV E w) n B n ≠ 0 := GlobalTheory.LFun.SatCompare.satEig_self_ne_zero hB
  have hI : (UpperTheory.V.Z.Tf.GlobalTraceComparison.inv B).card = n := by simpa [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv] using hB
  refine eq_of_satEig_eq (qV_ne_zero w) hI hB fun j hj => ?_
  have e := GlobalTheory.LFun.ConjPlace.satEig_inv_mul (q := qV E w) hB hj
  rw [← h j hj, mul_comm] at e
  exact mul_left_cancel₀ hne e

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.unitary_one_characters_separated_by_eigenvalues :
    SeparatesUnitaryOne := by
  intro E _ _ _ w a b B₁ B₂ h₁ h₂ hns
  by_cases hz : ∀ p : Fin (a + 1) × Fin (b + 1), ev2 a b w (dEx p) B₁ B₂ = 0
  · exfalso
    have hs₁ : satEig (qV E w) a B₁ a ≠ 0 := GlobalTheory.LFun.SatCompare.satEig_self_ne_zero h₁
    have hs₂ : satEig (qV E w) b B₂ b ≠ 0 := GlobalTheory.LFun.SatCompare.satEig_self_ne_zero h₂
    have key : ∀ p : Fin (a + 1) × Fin (b + 1),
        satEig (qV E w) a B₁ a * satEig (qV E w) b B₂ b *
            (satEig (qV E w) a B₁ p.1 * satEig (qV E w) b B₂ p.2) =
          satEig (qV E w) a B₁ (a - p.1) * satEig (qV E w) b B₂ (b - p.2) := by
      intro p
      have := hz p
      simp only [ev2, dEx, Ex.ev, Fin.val_last, Fin.val_rev] at this
      have e₁ : a + 1 - ((p.1 : ℕ) + 1) = a - p.1 := by omega
      have e₂ : b + 1 - ((p.2 : ℕ) + 1) = b - p.2 := by omega
      rw [e₁, e₂] at this
      linear_combination this
    refine hns ⟨inv_eq_of_eig w h₁ fun i hi => ?_, inv_eq_of_eig w h₂ fun j hj => ?_⟩
    · have := key (⟨i, Nat.lt_succ_of_le hi⟩, 0)
      simp only [Fin.val_zero, GlobalTheory.LFun.ConjPlace.satEig_zero, mul_one, Nat.sub_zero] at this
      refine mul_right_cancel₀ hs₂ ?_
      linear_combination this
    · have := key (0, ⟨j, Nat.lt_succ_of_le hj⟩)
      simp only [Fin.val_zero, GlobalTheory.LFun.ConjPlace.satEig_zero, one_mul, Nat.sub_zero] at this
      refine mul_left_cancel₀ hs₁ ?_
      linear_combination this
  · push_neg at hz
    obtain ⟨p, hp⟩ := hz
    refine ⟨_, U1.step (-(ev2 a b w (dEx p) B₁ B₂)⁻¹) p, ?_⟩
    have e : ev2 a b w (Ex.add Ex.one (Ex.smul (-(ev2 a b w (dEx p) B₁ B₂)⁻¹) (dEx p))) B₁ B₂ =
        1 + -(ev2 a b w (dEx p) B₁ B₂)⁻¹ * ev2 a b w (dEx p) B₁ B₂ := rfl
    rw [e, neg_mul, inv_mul_cancel₀ hp]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.UnStable
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem inv_map_sign (B : Multiset ℂˣ) (k : ℕ) (h : inv B = B) :
    inv (B.map (· * (-1 : ℂˣ) ^ k)) = B.map (· * (-1 : ℂˣ) ^ k) := by
  have hk : ((-1 : ℂˣ) ^ k)⁻¹ = (-1 : ℂˣ) ^ k := by
    rw [← inv_pow, inv_neg_one]
  conv_rhs => rw [← h]
  simp only [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv, Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  simp only [Function.comp_apply, mul_inv, hk]

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.unStable :
    UnStable := by
  intro E _ _ _ μ a b w B₁ B₂ hμ h₁ h₂
  have hadd : ∀ X Y : Multiset ℂˣ, inv (X + Y) = inv X + inv Y := fun X Y => Multiset.map_add _ _ _
  simp only [un, hμ]
  rw [hadd, inv_map_sign B₁ b h₁, inv_map_sign B₂ a h₂]
end

