module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrIdQ
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem trHl_id_apply (hHl : TrHl) (hL : TrLin) (hW : WtLin) (l : ℕ) [Fact l.Prime] (n i : ℤ) (S : Scheme.{0})
    (d : ℤ) (hu : IsUnit (l : Γ(S, ⊤))) (x : Hl l (sch.obj S) n i) :
    trHl l (𝟙 S) (Wt.const S d) n i x = d • x := by
  have hw : IsWt (𝟙 S) (Wt.const S d) := hW.2.2 (𝟙 S) d
  refine Subtype.ext (funext fun k => ?_)
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hu.pow k
  refine (hHl l n i (𝟙 S) _ hw hu x k).trans ?_
  exact (hL (l ^ k) n i).2.2 S d hq (x.1 k)

theorem UpperTheory.Gal.TranscendenceTraces.trIdQ_of :
    TrHl → TrLin → WtLin → TrIdQ := by
  intro hHl hL hW l _ n i S d hu
  unfold trHQ
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [LinearMap.baseChange_tmul, trHl_id_apply hHl hL hW l n i S d hu m]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.tmul_smul]
    rw [Int.cast_smul_eq_zsmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrLin
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem op_add_of (hRp : RpBasic) (hOp : RpOp) {q : ℕ} {i n : ℤ} {Z S : Scheme.{0}} {p : Z ⟶ S}
    (τ τ' σ : Fam p (res (ZMod q) (tw q i)) (res (ZMod q) (tw q i)))
    (h : ∀ a, (σ.deg n).app (Sq.self p) a = (τ.deg n).app (Sq.self p) a + (τ'.deg n).app (Sq.self p) a)
    (x : CohomologyClass ((chains (ZMod q)).obj (sch.obj Z)) (res (ZMod q) (tw q i)) n) :
    σ.op n x = τ.op n x + τ'.op n x := by
  obtain ⟨a, ha⟩ := ((hRp (ZMod q) (res (ZMod q) (tw q i)) Z n).1) x
  have h1 := hOp (ZMod q) (ZMod q) τ n x a ha
  have h2 := hOp (ZMod q) (ZMod q) τ' n x a ha
  have h3 := hOp (ZMod q) (ZMod q) σ n x a ha
  have hS := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1
  have h4 := (hS _ _ _ _ h1 h2).2.2.1
  exact (hS _ _ _ _ h3 h4).2.1 (h a)

private theorem op_smul_of (hRp : RpBasic) (hOp : RpOp) {q : ℕ} {i n : ℤ} {Z S : Scheme.{0}} {p : Z ⟶ S} (d : ℤ)
    (τ σ : Fam p (res (ZMod q) (tw q i)) (res (ZMod q) (tw q i)))
    (h : ∀ a, (σ.deg n).app (Sq.self p) a = d • (τ.deg n).app (Sq.self p) a)
    (x : CohomologyClass ((chains (ZMod q)).obj (sch.obj Z)) (res (ZMod q) (tw q i)) n) :
    σ.op n x = d • τ.op n x := by
  obtain ⟨a, ha⟩ := ((hRp (ZMod q) (res (ZMod q) (tw q i)) Z n).1) x
  have h1 := hOp (ZMod q) (ZMod q) τ n x a ha
  have h3 := hOp (ZMod q) (ZMod q) σ n x a ha
  have hS := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1
  have h4 := (hS _ _ _ _ h1 h1).2.2.2 d
  exact (hS _ _ _ _ h3 h4).2.1 (h a)

private theorem op_id_of (hRp : RpBasic) (hOp : RpOp) {q : ℕ} {i n : ℤ} {S : Scheme.{0}} (d : ℤ)
    (σ : Fam (𝟙 S) (res (ZMod q) (tw q i)) (res (ZMod q) (tw q i)))
    (h : ∀ a, (σ.deg n).app (Sq.self (𝟙 S)) a = d • a)
    (x : CohomologyClass ((chains (ZMod q)).obj (sch.obj S)) (res (ZMod q) (tw q i)) n) :
    σ.op n x = d • x := by
  obtain ⟨a, ha⟩ := ((hRp (ZMod q) (res (ZMod q) (tw q i)) S n).1) x
  have h3 := hOp (ZMod q) (ZMod q) σ n x a ha
  have hS := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1
  have h4 := (hS _ _ _ _ ha ha).2.2.2 d
  exact (hS _ _ _ _ h3 h4).2.1 (h a)

theorem UpperTheory.Gal.TranscendenceTraces.trLin_of :
    TrChar → FamLin → WtLin → RpBasic → RpOp → TrLin := by
  intro hChar hFam hWt hRp hOp q _ n i
  refine ⟨?_, ?_, ?_⟩
  · intro Z S p _ w w' hw hw' hq x
    obtain ⟨σ, hσ, hσd⟩ := (hFam q i).1 p w w' (trFam p w q i) (trFam p w' q i)
      (hChar q i p w hw hq).2.1 (hChar q i p w' hw' hq).2.1
    rw [(hChar q i p (w.add w') (hWt.1 p w w' hw hw') hq).2.2 σ hσ n]
    exact op_add_of hRp hOp _ _ σ (fun a => hσd n _ a) x
  · intro Z S p _ d w hw hq x
    obtain ⟨σ, hσ, hσd⟩ := (hFam q i).2.1 p d w (trFam p w q i) (hChar q i p w hw hq).2.1
    rw [(hChar q i p (w.smul d) (hWt.2.1 p d w hw) hq).2.2 σ hσ n]
    exact op_smul_of hRp hOp d _ σ (fun a => hσd n _ a) x
  · intro S d hq x
    obtain ⟨σ, hσ, hσd⟩ := (hFam q i).2.2 S d
    rw [(hChar q i (𝟙 S) (Wt.const S d) (hWt.2.2 (𝟙 S) d) hq).2.2 σ hσ n]
    exact op_id_of hRp hOp d σ (fun a => hσd n a) x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrPush
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trPush_of :
    TrChar → FamPush → WtPush → RpBasic → RpOp → TrPush := by
  intro hTr hFam hWt hRp hOp q _ n i Z Z' S h p _ _ w hw hq x
  obtain ⟨σ, hσ, hσd⟩ := hFam q i h p w (trFam (h ≫ p) w q i) (hTr q i (h ≫ p) w hw hq).2.1
  have hw' := hWt h p w hw
  have e2 : tr p (Wt.push h w) q n i = σ.op n := by
    ext y
    exact (hTr q i p (Wt.push h w) hw' hq).2.2 σ hσ n ▸ rfl
  rw [e2]
  obtain ⟨a, ha⟩ := (hRp (ZMod q) (res (ZMod q) (tw q i)) Z' n).1 x
  have h1 := hOp (ZMod q) (ZMod q) σ n x a ha
  have h2 := hOp (ZMod q) (ZMod q) (trFam (h ≫ p) w q i) n _ _
    ((hRp (ZMod q) (res (ZMod q) (tw q i)) Z' n).2.2.2.1 Z h x a ha)
  exact ((hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1 _ _ _ _ h2 h1).2.1 (hσd n a).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrRel
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private noncomputable def wSum {Z : Scheme.{0}} {ι : Type} (w : ι → Wt Z) (m : ι → ℤ) (s : Finset ι) : Wt Z :=
  fun Ω _ _ z => ∑ a ∈ s, m a * w a Ω z

theorem UpperTheory.Gal.TranscendenceTraces.trRel_of :
    TrLin → WtLin → WtVanish → TrRel := by
  intro hT hW hV q _ n i Z S p _ ι _ w m hw hq D hD hz x
  classical
  obtain ⟨hTa, hTs, -⟩ := hT q n i
  obtain ⟨hWa, hWs, -⟩ := hW
  have h0 : wSum w m ∅ = Wt.const Z 0 := by
    funext Ω _ _ z
    simp [wSum, Wt.const]
  have hc : ∀ y : Ht q (sch.obj Z) n i, tr p (Wt.const Z 0) q n i y = 0 := by
    intro y
    have hs : Wt.smul 0 (Wt.const Z 0) = Wt.const Z 0 := by
      funext Ω _ _ z
      simp [Wt.smul, Wt.const]
    rw [← hs, hTs p 0 _ (isWt_zero p) hq y, zero_smul]
  have hins : ∀ (a : ι) (s : Finset ι), a ∉ s →
      wSum w m (insert a s) = (Wt.smul (m a) (w a)).add (wSum w m s) := by
    intro a s ha
    funext Ω _ _ z
    simp [wSum, Wt.add, Wt.smul, Finset.sum_insert ha]
  have key : ∀ s : Finset ι, IsWt p (wSum w m s) ∧
      ∀ y, tr p (wSum w m s) q n i y = ∑ a ∈ s, m a • tr p (w a) q n i y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [h0]
      exact ⟨isWt_zero p, fun y => by rw [hc y, Finset.sum_empty]⟩
    | insert a s ha ih =>
      rw [hins a s ha]
      have h1 := hWs p (m a) (w a) (hw a)
      refine ⟨hWa p _ _ h1 ih.1, fun y => ?_⟩
      rw [hTa p _ _ h1 ih.1 hq y, hTs p _ _ (hw a) hq y, ih.2 y, Finset.sum_insert ha]
  have hzero : wSum w m Finset.univ = Wt.const Z 0 :=
    hV p _ (key Finset.univ).1 D hD fun Ω _ _ z hz' => hz Ω z hz'
  rw [← (key Finset.univ).2 x, hzero, hc x]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrSplitQ
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem pullHQ_id' (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) :
    pullHQ l (𝟙 E) n i = LinearMap.id := by
  unfold pullHQ
  rw [pullHl_id, LinearMap.baseChange_id]

private theorem pullHQ_comp' (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = (pullHQ l f n i) ∘ₗ (pullHQ l g n i) := by
  unfold pullHQ
  rw [pullHl_comp, LinearMap.baseChange_comp]

private theorem existsUnique_sec {U P : Scheme.{0}} (p' : P ⟶ U) {m : ℕ} (s' : Fin m → (U ⟶ P))
    (hs : ∀ j, s' j ≫ p' = 𝟙 U) (hiso : IsIso (Sigma.desc s' : ∐ (fun _ : Fin m => U) ⟶ P))
    {Ω : Type} [Field Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P) (hy : y ≫ p' = x0) :
    ∃! j, x0 ≫ s' j = y := by
  have hι : ∀ j, Sigma.ι (fun _ : Fin m => U) j ≫ Sigma.desc s' = s' j := fun j => Sigma.ι_desc _ _
  let t : gp Ω ⟶ ∐ (fun _ : Fin m => U) := y ≫ inv (Sigma.desc s')
  obtain ⟨⟨j, u⟩, hu⟩ := (sigmaMk (fun _ : Fin m => U)).surjective (pt t)
  rw [sigmaMk_mk] at hu
  have hr : Set.range t ⊆ Set.range (Sigma.ι (fun _ : Fin m => U) j) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨u, by rw [hu, pt_eq]⟩
  let t' := IsOpenImmersion.lift (Sigma.ι (fun _ : Fin m => U) j) t hr
  have ht' : t' ≫ Sigma.ι (fun _ : Fin m => U) j = t := IsOpenImmersion.lift_fac _ _ _
  have h1 : t' ≫ s' j = y := by
    rw [← hι j, ← Category.assoc, ht']
    simp [t]
  have h2 : t' = x0 := by
    rw [← hy, ← h1, Category.assoc, hs j, Category.comp_id]
  refine ⟨j, by rw [← h2]; exact h1, fun k hk => ?_⟩
  have h3 : (x0 ≫ Sigma.ι (fun _ : Fin m => U) k) ≫ Sigma.desc s' =
      (x0 ≫ Sigma.ι (fun _ : Fin m => U) j) ≫ Sigma.desc s' := by
    rw [Category.assoc, Category.assoc, hι, hι, hk, ← h2, h1]
  have h4 := (cancel_mono (Sigma.desc s')).1 h3
  have h5 : Sigma.ι (fun _ : Fin m => U) k (pt x0) = Sigma.ι (fun _ : Fin m => U) j (pt x0) := by
    rw [← pt_comp, ← pt_comp, h4]
  exact congrArg Sigma.fst ((sigmaι_eq_iff _ k j _ _).1 h5)

private theorem finsum_one_singleton {T : Type*} (A : Set T) (a : T) (h : A = {a}) :
    ∑ᶠ z ∈ A, (1 : ℤ) = 1 := by
  subst h
  simp

private theorem finsum_one_empty {T : Type*} (A : Set T) (h : A = ∅) :
    ∑ᶠ z ∈ A, (1 : ℤ) = 0 := by
  subst h
  simp

private theorem tr_split (hCorr : CorrEqQ) (hId : TrIdQ) (l : ℕ) [Fact l.Prime] (n i : ℤ) {U P : Scheme.{0}}
    (p' : P ⟶ U) [IsFinite p'] (wt : IsWt p' (Wt.const P 1)) (wt1 : IsWt (𝟙 U) (Wt.const U 1))
    (hl : IsUnit (l : Γ(U, ⊤))) {m : ℕ} (s' : Fin m → (U ⟶ P)) (hs : ∀ j, s' j ≫ p' = 𝟙 U)
    (hiso : IsIso (Sigma.desc s' : ∐ (fun _ : Fin m => U) ⟶ P)) :
    trHQ l p' (Wt.const P 1) n i = ∑ j, pullHQ l (sch.map (s' j)) n i := by
  classical
  let c : Option (Fin m) → Corr U P := fun o => match o with
    | none => ⟨P, p', 𝟙 P, Wt.const P 1, inferInstance, wt⟩
    | some j => ⟨U, 𝟙 U, s' j, Wt.const U 1, inferInstance, wt1⟩
  let mm : Option (Fin m) → ℤ := fun o => match o with
    | none => 1
    | some _ => -1
  have hcn : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P),
      (c none).cyc Ω x0 y = if y ≫ p' = x0 then 1 else 0 := by
    intro Ω _ _ x0 y
    split_ifs with h
    · refine finsum_one_singleton _ y ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_singleton_iff, Category.comp_id]
      exact ⟨fun hz => hz.2, fun hz => ⟨hz ▸ h, hz⟩⟩
    · refine finsum_one_empty _ ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Category.comp_id]
      rintro ⟨h1, rfl⟩
      exact h h1
  have hcs : ∀ (j : Fin m) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P),
      (c (some j)).cyc Ω x0 y = if x0 ≫ s' j = y then 1 else 0 := by
    intro j Ω _ _ x0 y
    split_ifs with h
    · refine finsum_one_singleton _ x0 ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_singleton_iff, Category.comp_id]
      exact ⟨fun hz => hz.1, fun hz => ⟨hz, hz ▸ h⟩⟩
    · refine finsum_one_empty _ ?_
      ext z
      simp only [c, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Category.comp_id]
      rintro ⟨rfl, h1⟩
      exact h h1
  have key := hCorr l n i (𝟙 U) p' (Option (Fin m)) c mm
    (fun a => by cases a with
      | none => simp [c]
      | some j => simp [c, hs j]) hl Set.univ dense_univ
    (fun Ω _ _ x0 y _ => by
      rw [Fintype.sum_option]
      simp only [hcn, hcs, mm]
      by_cases hy : y ≫ p' = x0
      · obtain ⟨j, hj, hu⟩ := existsUnique_sec p' s' hs hiso x0 y hy
        rw [if_pos hy, Finset.sum_eq_single j]
        · simp [hj]
        · intro k _ hk
          rw [if_neg (fun e => hk (hu k e))]
          simp
        · simp
      · rw [if_neg hy]
        simp only [mul_zero, zero_add]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [if_neg]
        · simp
        · intro e
          apply hy
          rw [← e, Category.assoc, hs j, Category.comp_id])
  rw [Fintype.sum_option] at key
  have e0 : (c none).opQ l n i = trHQ l p' (Wt.const P 1) n i := by
    change trHQ l p' (Wt.const P 1) n i ∘ₗ pullHQ l (sch.map (𝟙 P)) n i = _
    rw [CategoryTheory.Functor.map_id, pullHQ_id', LinearMap.comp_id]
  have e1 : ∀ j, (c (some j)).opQ l n i = pullHQ l (sch.map (s' j)) n i := by
    intro j
    change trHQ l (𝟙 U) (Wt.const U 1) n i ∘ₗ pullHQ l (sch.map (s' j)) n i = _
    rw [hId l n i U 1 hl]
    simp
  simp only [mm, e0, e1] at key
  simp only [Int.cast_one, one_smul, Int.cast_neg, neg_smul, Finset.sum_neg_distrib] at key
  exact add_neg_eq_zero.1 key

theorem UpperTheory.Gal.TranscendenceTraces.trSplitQ_of :
    TrBCQ → CorrEqQ → TrIdQ → WtLin → WtFlat → MultBasic → TrSplitQ := by
  intro hBC hCorr hId hLin hFlat hMult l _ n i Z S p _ _ hl U x m s hs hiso
  have wtp : IsWt p (Wt.const Z 1) := by
    rw [← hMult.2.2 p]
    exact hFlat p
  have wtp' : IsWt (pullback.snd p x) (Wt.const (pullback p x) 1) := by
    rw [← hMult.2.2 (pullback.snd p x)]
    exact hFlat _
  have hlU : IsUnit (l : Γ(U, ⊤)) := by
    simpa using hl.map x.appTop.hom
  have h1 := hBC l n i (pullback.fst p x) (pullback.snd p x) p x (Wt.const Z 1)
    (IsPullback.of_hasPullback p x) wtp hl
  have h2 := tr_split hCorr hId l n i (pullback.snd p x) wtp' (hLin.2.2 (𝟙 U) 1) hlU
    (fun j => pullback.lift (s j) (𝟙 U) (by rw [hs j, Category.id_comp]))
    (fun j => pullback.lift_snd _ _ _) hiso
  rw [h1]
  change trHQ l (pullback.snd p x) (Wt.const _ 1) n i ∘ₗ _ = _
  rw [h2]
  refine LinearMap.ext fun a => ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← LinearMap.comp_apply, ← pullHQ_comp', ← CategoryTheory.Functor.map_comp, pullback.lift_fst]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrSum
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trSum_of :
    SumEx → SumNat → PtInj → FibFin → TrSum := by
  intro hEx hNat hInj hFin q _ i Z S p _ w hw hq
  have uniq : ∀ (A : Sq p) (a : Sec (tw q i) A.V) (b b' : Sec (tw q i) A.U),
      IsSum w A a b → IsSum w A a b' → b = b' := by
    intro A a b b' hb hb'
    apply hInj q i A.U b b'
    intro Ω _ _ x
    rw [hb Ω x, hb' Ω x]
  have ex : ∃ t : Fam0 p (tw q i) (tw q i),
      ∀ (A : Sq p) (a : Sec (tw q i) A.V), IsSum w A a (t.app A a) := by
    choose f hf using fun (A : Sq p) (a : Sec (tw q i) A.V) => hEx q i p w hw hq A a
    refine ⟨⟨fun A => { toFun := f A, map_zero' := ?_, map_add' := ?_ }, ?_⟩, ?_⟩
    · refine uniq A 0 _ _ (hf A 0) ?_
      intro Ω _ _ x
      simp [Sec.res]
    · intro a a'
      refine uniq A (a + a') _ _ (hf A (a + a')) ?_
      intro Ω _ _ x
      have hfin : (fib A.r x).Finite := by
        haveI := Sq.finite A
        exact hFin A.r Ω x
      rw [show Sec.res x (f A a + f A a') = Sec.res x (f A a) + Sec.res x (f A a') by simp [Sec.res],
        hf A a Ω x, hf A a' Ω x, ← finsum_mem_add_distrib hfin]
      apply finsum_mem_congr rfl
      intro z _
      simp [Sec.res, smul_add]
    · intro A B t a
      exact uniq A (Sec.res t.k a) _ _ (hNat _ (tw q i) w t a (f B a) (hf B a)) (hf A _)
    · intro A a
      exact hf A a
  exact pick_spec ex
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtClopen
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem isLocallyConstant_weighted_sum {X : Type*} [TopologicalSpace X] (T : Finset ℤ) (f : ℤ → X → ℤ)
    (hf : ∀ c, IsLocallyConstant (f c)) : IsLocallyConstant (fun y => ∑ c ∈ T, c * f c y) := by
  have h : ∀ c, Continuous (f c) := fun c => (IsLocallyConstant.iff_continuous _).1 (hf c)
  exact (IsLocallyConstant.iff_continuous _).2
    (continuous_finsetSum _ fun c _ => continuous_const.mul (h c))

theorem UpperTheory.Gal.TranscendenceTraces.wtClopen_of :
    WtCrit → FibFin → WtClopen := by
  intro hcrit hfin Z S p _ w hcl
  apply hcrit p w
  intro A φ hφ u
  have hφc : Continuous φ := (IsLocallyConstant.iff_continuous φ).1 hφ
  haveI := A.finite
  obtain ⟨U0, hU0, hu, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 A.U.isBasis_affineOpens)
    (show u ∈ (⊤ : A.U.Opens) from trivial)
  have hK : IsCompact (A.r ⁻¹' (U0 : Set A.U)) :=
    QuasiCompact.isCompact_preimage _ U0.isOpen (IsAffineOpen.isCompact hU0)
  let T : Finset ℤ := ((hK.image hφc).finite_of_discrete).toFinset
  choose ψ hψ hψs using fun c : ℤ => hcl A (φ ⁻¹' {c}) (hφ.isClopen_fiber c)
  let Ψ : A.U → ℤ := fun y => ∑ c ∈ T, c * ψ c y
  have hΨ : IsLocallyConstant Ψ := isLocallyConstant_weighted_sum T ψ hψ
  refine ⟨(U0 : Set A.U) ∩ {y | Ψ y = Ψ u}, Ψ u, U0.isOpen.inter (hΨ.isOpen_fiber _),
    ⟨hu, rfl⟩, ?_⟩
  rintro Ω _ _ x ⟨hx0, hxΨ⟩
  rw [← show Ψ (pt x) = Ψ u from hxΨ]
  have hF := hfin A.r Ω x
  classical
  have key : ∀ c, ψ c (pt x) =
      ∑ z ∈ hF.toFinset, if φ (pt z) = c then w Ω (z ≫ A.v) else 0 := by
    intro c
    rw [hψs c Ω x, finsum_mem_eq_finite_toFinset_sum _ (hF.inter_of_left _), ← Finset.sum_filter]
    congr 1
    ext z
    simp
  simp only [Ψ, key, Finset.mul_sum]
  rw [finsum_mem_eq_finite_toFinset_sum _ hF, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  have hzf : z ≫ A.r = x := (Set.Finite.mem_toFinset hF).1 hz
  have hmem : φ (pt z) ∈ T := by
    rw [Set.Finite.mem_toFinset]
    refine ⟨pt z, ?_, rfl⟩
    show A.r (pt z) ∈ (U0 : Set A.U)
    rw [← pt_comp, hzf]
    exact hx0
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, if_pos hmem, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtComp
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtComp_of :
    SumComp → FibFin → WtComp := by
  intro hsum hfin W Z S r p _ _ w' w hr hp A φ hφ
  obtain ⟨m, hm1, hm2⟩ : ∃ m : A.V ⟶ pullback p A.u,
      m ≫ pullback.fst p A.u = A.v ≫ r ∧ m ≫ pullback.snd p A.u = A.r :=
    ⟨pullback.lift (A.v ≫ r) A.r (by rw [Category.assoc]; exact A.pb.w),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hsq : IsPullback A.v m r (pullback.fst p A.u) := by
    refine IsPullback.of_bot ?_ hm1.symm (IsPullback.of_hasPullback p A.u)
    rw [hm2]
    exact A.pb
  let C : Sq r := ⟨pullback p A.u, A.V, pullback.fst p A.u, A.v, m, hsq⟩
  haveI : IsFinite m := C.finite
  haveI : IsFinite (pullback.snd p A.u) := (Sq.of p A.u).finite
  obtain ⟨ψ1, hψ1, hψ1s⟩ := hr C φ hφ
  obtain ⟨ψ2, hψ2, hψ2s⟩ := hp (Sq.of p A.u) ψ1 hψ1
  refine ⟨ψ2, hψ2, ?_⟩
  intro Ω _ _ x
  have hsc : ∀ c : (gp Ω ⟶ A.V) → ℤ, ∑ᶠ z ∈ fib (m ≫ pullback.snd p A.u) x, c z =
      ∑ᶠ y ∈ fib (pullback.snd p A.u) x, ∑ᶠ z ∈ fib m y, c z := by
    intro c
    have h := congrArg (AddEquiv.ulift : ULift.{1} ℤ ≃+ ℤ)
      (hsum m (pullback.snd p A.u) Ω x (ULift.{1} ℤ) (fun z => ULift.up (c z)))
    simp only [AddEquiv.map_finsum] at h
    exact h
  refine (hψ2s Ω x).trans ?_
  rw [← hm2, hsc]
  refine finsum_mem_congr rfl ?_
  intro y _
  refine (congrArg (fun t => w Ω (y ≫ pullback.fst p A.u) * t) (hψ1s Ω y)).trans ?_
  rw [mul_finsum_mem]
  refine finsum_mem_congr rfl ?_
  intro z hz
  have hz' : z ≫ m = y := hz
  show w Ω (y ≫ pullback.fst p A.u) * (w' Ω (z ≫ A.v) * φ (pt z)) =
    w' Ω (z ≫ A.v) * w Ω ((z ≫ A.v) ≫ r) * φ (pt z)
  rw [Category.assoc, ← hm1, ← Category.assoc, hz']
  exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtCrit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtCrit_of :
    PtEx → WtCrit := by
  intro hPt Z S p w h A φ hφ
  choose N c hN hu hc using h A φ hφ
  refine ⟨c, ?_, fun Ω _ _ x => (hc (pt x) Ω x (hu (pt x))).symm⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro u
  refine ⟨N u, hN u, hu u, fun u' hu' => ?_⟩
  obtain ⟨Ω, _, _, x, rfl⟩ := hPt A.U u'
  rw [← hc (pt x) Ω x (hu (pt x)), hc u Ω x hu']
end

