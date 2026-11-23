module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SatakeTwists.SatakeTwistHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.AbsInf
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.absInf :
    AbsInf := by
  intro E _ _ _ N P z τ
  have key : (P.twist (Model.absC E z)).infChar τ = (P.infChar τ).map (· + z) := by
    have e := ((ParLaws.hasInfChar_infChar P τ).twist (Model.absC E z)).infChar_eq
    rw [Model.expo_absC] at e
    exact e
  exact ⟨key, key⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.AsmThOf
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.asmTh_of :
    Choice → (USide → UEval) → (MatchUnit → MatchSplit → FamMatch) → Ends → TwDataT → RegOf → UnStable → MuInf → CsdInert → Sep → RegCt → TrAvg → Places → AsmTh := by
  intro hC hUE hF hEn hTw hRO hUS hMI hCI hSep hReg hTr hP hU hG hMu hM1 hM3 hE hS E _ _ _ hunr n hn π hreg hd hsph
  obtain ⟨μ, e, hμ⟩ := hMu E hunr
  obtain ⟨lam, hst⟩ := hS E hunr n hn π hreg hd
  obtain ⟨S, Z, B, τ, f, hS', hZ, hB, hf, w₀, hw₀, hr₀⟩ := hC E n hn π hsph μ e hμ
  obtain ⟨K', ι, _, σ, A, BU, hK, hσ, hUv⟩ := hUE hU E hunr n hn S hS' lam Z hZ f (fun w hw => (hf w hw).2.1) ⟨w₀, hw₀, hr₀⟩
  have hFM := hF hM1 hM3 E hunr n μ e hμ S hS' Z hZ (fun w hw => (hB w hw).2) f fun w hw => (hf w hw).2.1
  have hLc := fun a b h => (hFM a b h).1
  choose t ht using fun a b h => (hFM a b h).2
  have hRg : ∀ a b (h : a + b = n), ∃ w ∈ Z, RegAt2 a b w (ct0 μ h f w) := fun a b h =>
    ⟨w₀, hw₀, hReg E w₀ (hZ w₀ hw₀).2 μ n a b h f hr₀⟩
  obtain ⟨κ, _, a, l₁, l₂, sg, hw, ⟨i₁, ha₁, hs₁, hu₁⟩, ⟨i₀, ha₀, hs₀, hu₀⟩, hid⟩ := hG E hunr n hn μ e hμ lam
  have hab : ∀ i, a i + (n - a i) = n := fun i => Nat.add_sub_cancel' (hw i).1
  obtain ⟨l₀⟩ : Nonempty (InfinitePlace E → DomWeight 0) := ⟨fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩
  obtain ⟨c, hc, hst⟩ := hst l₀ S hS' Z hZ B τ (fun w hw => (hB w hw).1) fun w hw => (hf w hw).1
  obtain ⟨Js, _, Ds, Bs, hDs, hDsI, hDsS, hst⟩ := hst (ct0 μ (Nat.add_zero n) f) (hLc n 0 _) (hRg n 0 _)
  choose J hJ D₁ D₂ B₁ B₂ hD hDI hDS hEb using fun i => hE E hunr (a i) (n - a i) (by rw [hab i]; exact hn) S hS' (l₁ i) (l₂ i) Z hZ
    (ct0 μ (hab i) f) (hLc _ _ _) (hRg _ _ _)
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hcA, hcB⟩ := hcon
  have hoff := off_cofinite hP Z
  have hBst : ∀ᶠ w : Pl E in cofinite, ¬ IsSplitAt w → inv (B w) = B w :=
    ((hCI E n hn π hd).and hoff).mono fun w h hns => h.1 hns _ (hB w h.2).1
  let I : Type := ι ⊕ Js ⊕ (Σ i : {i : κ // 1 ≤ a i ∧ 1 ≤ n - a i}, J i.1)
  let C : I → Pl E → Multiset ℂˣ := Sum.elim BU (Sum.elim Bs fun p w => un μ (a p.1.1) (n - a p.1.1) w (B₁ p.1.1 p.2 w) (B₂ p.1.1 p.2 w))
  have hdat : ∀ (D : CD E n) (X : Pl E → Multiset ℂˣ), ¬ D.Has π → D.Reg →
      (∀ᶠ w : Pl E in cofinite, ¬ IsSplitAt w → inv (X w) = X w) → (∀ w, Off Z w → D.Sat w (X w)) →
      ∃ w, Off Z w ∧ IsSplitAt w ∧ (B w).card = n ∧ (X w).card = n ∧ X w ≠ B w := fun D X h1 hr hs h2 => by
    by_contra h
    refine hcB ⟨D, h1, hr, (hoff.and hs).mono fun w hx hns => ⟨X w, h2 w hx.1, hx.2 hns⟩,
      hoff.mono fun w ho hs => ⟨B w, ?_, (hB w ho).1⟩⟩
    have : X w = B w := by_contra fun h' => h ⟨w, ho, hs, (hB w ho).1.card, sat_card (h2 w ho), h'⟩
    exact this ▸ h2 w ho
  obtain ⟨T, e₁, e₂, hT, hTZ, hv1, hv0⟩ := hSep E n S hS' Z I B C (by
    rintro (i | j | ⟨i, j⟩)
    · by_contra h
      refine hcA ⟨σ i, (hσ i).1, (hσ i).2.1, hoff.mono fun w ho hs => ?_⟩
      obtain ⟨τ', a1, a2⟩ := (hσ i).2.2 w ho hs
      have : BU i w = B w := by_contra fun h' => h ⟨w, ho, hs, (hB w ho).1.card, a2.card, h'⟩
      exact ⟨τ', B w, a1, this ▸ a2, (hB w ho).1⟩
    · exact hdat (Ds j) (Bs j) (hDs j).1 (hRO E n lam (Ds j) (hDsI j))
        (hBst.mono fun w h hns => hDsS j w hns (h hns)) (hDs j).2
    · obtain ⟨D, h1, hr, h2⟩ := hTw E n _ _ (hab i.1) i.2.1 i.2.2 μ e hμ (l₁ i.1) (l₂ i.1) lam (hw i.1).2
        (D₁ i.1 j) (D₂ i.1 j) (hDI i.1 j).1 (hDI i.1 j).2
      exact hdat D _ (h1 π) hr
        (Filter.Eventually.of_forall fun w hns => hUS E μ _ _ w _ _ ((hMI E μ e hμ).1 w hns)
          (hDS i.1 j w hns).1 (hDS i.1 j w hns).2)
        fun w ho => h2 w _ _ (hB w ho).2 (hD i.1 j w ho).1 (hD i.1 j w ho).2)
  have un0 : ∀ X : Pl E → Multiset ℂˣ, (fun w => un μ n 0 w (X w) ((0 : Pl E → Multiset ℂˣ) w)) = X := fun X => by
    funext w; simp [un]
  let Φ := fun (a b : ℕ) (h : a + b = n) (k : ℕ) =>
    fam Z T (ct0 μ h f) (fun w => (e₁ w).bind (t a b h w)) (fun w => (e₂ w).bind (t a b h w)) k
  set P : ℂ := c * ∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => ct0 μ (Nat.add_zero n) f w (g, 1) with hPdef
  have hP0 : P ≠ 0 := mul_ne_zero hc (Finset.prod_ne_zero_iff.2 fun w hw => by
    rw [hTr E n w (hZ w hw).2 μ (τ w) f (hf w hw).2.1]; exact (hf w hw).2.2)
  have hSt : Tendsto (fun k => geomSt2 S lam l₀ (Φ n 0 (Nat.add_zero n) k)) atTop (𝓝 P) := by
    have h1 := small_tendsto (hst T hT hTZ _ _ (1 / 2) (by norm_num) fun j => by
      rw [(ht n 0 (Nat.add_zero n) T hT hTZ e₁ e₂).1 _ _ fun w ho => ⟨sat_card ((hDs j).2 w ho), rfl⟩, un0]
      have := hv0 (.inr (.inl j))
      simp only [C, Sum.elim_inr, Sum.elim_inl] at this
      rw [this]; norm_num)
    rw [(ht n 0 (Nat.add_zero n) T hT hTZ e₁ e₂).1 _ _ fun w ho => ⟨(hB w ho).1.card, rfl⟩, un0, hv1] at h1
    have h2 := h1.add_const P
    simpa [hPdef, Φ] using h2
  have hterm : ∀ i, Tendsto (fun k => ((sg i : ℤ) : ℂ) * geomSt2 S (l₁ i) (l₂ i) (Φ _ _ (hab i) k)) atTop
      (𝓝 (if 1 ≤ a i ∧ 1 ≤ n - a i then 0 else P)) := fun i => by
    split_ifs with hm
    · have h1 := small_tendsto (hEb i T hT hTZ _ _ (1 / 2) (by norm_num) fun j => by
        rw [(ht _ _ (hab i) T hT hTZ e₁ e₂).1 _ _ fun w ho => ⟨sat_card (hD i j w ho).1, sat_card (hD i j w ho).2⟩]
        have := hv0 (.inr (.inr ⟨⟨i, hm⟩, j⟩))
        simp only [C, Sum.elim_inr] at this
        rw [this]; norm_num)
      simpa using h1.const_mul ((sg i : ℤ) : ℂ)
    · have h0 : a i = 0 ∨ n - a i = 0 := by omega
      have hs : sg i = 1 := by
        rcases h0 with h | h
        · rw [hu₀ i h]; exact hs₀
        · rw [hu₁ i (by have := hab i; omega)]; exact hs₁
      refine hSt.congr fun k => ?_
      rw [hs, hEn E n _ _ (hab i) h0 μ e S (l₁ i) (l₂ i) lam l₀ (famU Z T f e₁ e₂ k) _ _ (hw i).2
        (fun w hw => (((ht _ _ (hab i) T hT hTZ e₁ e₂).2 k).2 w hw).2)
        (fun w hw => (((ht _ _ (Nat.add_zero n) T hT hTZ e₁ e₂).2 k).2 w hw).2)]
      simp [Φ]
  have hsum := tendsto_finsetSum Finset.univ fun i _ => hterm i
  have hzero : ∀ k, 1 ≤ k → ∑ i, ((sg i : ℤ) : ℂ) * geomSt2 S (l₁ i) (l₂ i) (Φ _ _ (hab i) k) = 0 := fun k hk => by
    have h1 := hid S hS' K' (famU Z T f e₁ e₂ k) (fun a' => if h : a' + (n - a') = n then Φ a' (n - a') h k else 0) hK
      (hUv T hT hTZ e₁ e₂ k).1 fun a' ha' => by
        have h := Nat.add_sub_cancel' ha'
        simp only [dif_pos h]
        exact ⟨((ht _ _ h T hT hTZ e₁ e₂).2 k).1, fun w hw => (((ht _ _ h T hT hTZ e₁ e₂).2 k).2 w hw).1⟩
    rw [(hUv T hT hTZ e₁ e₂ k).2] at h1
    simp only [dif_pos (hab _)] at h1
    rw [← h1]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := hv0 (.inl i)
    simp only [C, Sum.elim_inl] at this
    rw [this, zero_pow (by omega), mul_zero]
  have hlim := tendsto_nhds_unique hsum (tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun k hk => (hzero k hk).symm))
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul] at hlim
  refine mul_ne_zero (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i₀, ?_⟩)) hP0 hlim
  simp [ha₀]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.CdAddG
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.cdAddG :
    CDAddG := by
  intro E _ _ _ r s D₁ D₂ ν ν' hr hs
  let e : Fin (D₁.c + D₂.c) ≃ Fin D₁.c ⊕ Fin D₂.c := finSumFinEquiv.symm
  let Q : Fin D₁.c ⊕ Fin D₂.c → Σ k, CG E k := Sum.elim (fun i => ⟨_, (D₁.P i).twist ν⟩) fun i => ⟨_, (D₂.P i).twist ν'⟩
  refine ⟨⟨D₁.c + D₂.c, fun i => (Q (e i)).1, fun i => (Q (e i)).2, fun i => ?_, ?_⟩, fun π hπ => ?_,
    fun w B₁ B₂ h h' ⟨b₁, c₁, d₁⟩ ⟨b₂, c₂, d₂⟩ => ⟨fun i => Sum.elim (fun i => (b₁ i).map (· * ν.val w))
      (fun i => (b₂ i).map (· * ν'.val w)) (e i), fun i : Fin (D₁.c + D₂.c) => ?_, ?_⟩, fun τ => ?_⟩
  · rcases e i with i | i
    exacts [D₁.pos i, D₂.pos i]
  · rw [e.sum_comp fun o => (Q o).1, Fintype.sum_sum_type]
    exact congrArg₂ (· + ·) D₁.sum D₂.sum
  · obtain ⟨i, hi⟩ := hπ
    have h1 : (Q (e i)).1 = r + s := congrArg Sigma.fst hi
    revert h1
    rcases e i with i | i
    · intro h1
      have h2 : D₁.N i ≤ r := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans D₁.sum.le
      have h3 : D₁.N i = r + s := h1
      omega
    · intro h1
      have h2 : D₂.N i ≤ s := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans D₂.sum.le
      have h3 : D₂.N i = r + s := h1
      omega
  · show (Q (e i)).2.HasSat w (Sum.elim (fun i => (b₁ i).map (· * ν.val w)) (fun i => (b₂ i).map (· * ν'.val w)) (e i))
    rcases e i with i | i
    exacts [PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ h (c₁ i), PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ h' (c₂ i)]
  · show ∑ i : Fin (D₁.c + D₂.c), _ = _
    rw [e.sum_comp (Sum.elim (fun i => (b₁ i).map (· * ν.val w)) fun i => (b₂ i).map (· * ν'.val w)), Fintype.sum_sum_type,
      ← d₁, ← d₂]
    exact congrArg₂ (· + ·) (map_sum (Multiset.mapAddMonoidHom _) _ _).symm (map_sum (Multiset.mapAddMonoidHom _) _ _).symm
  · show ∑ i : Fin (D₁.c + D₂.c), (Q (e i)).2.infChar τ = _
    rw [e.sum_comp fun o => (Q o).2.infChar τ, Fintype.sum_sum_type]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.CsdInert
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.csdInert :
    GOne.CsdSat → CsdInert := by
  intro h E _ _ _ n hn π hd
  filter_upwards [h E n hn π hd] with w hw hns B hB
  obtain ⟨B₀, hB₀, hc⟩ := hw
  obtain rfl := CG.HasSat.unique hB hB₀
  exact CG.HasSat.unique (hc w ⟨rfl, Or.inr hns⟩) hB
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.CtCaseJ
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.ctCaseJ :
    StepT → SplitLim → SatComb → CDAddG → AbsInf → MToLaws → CtCaseJ := by
  intro hS hL hC hA hI hM E _ _ _ r s hr hs bad ih₁ ih₂ K W m₀ X hK hW
  obtain ⟨K₁, W₁, K₂, W₂, l₁, f₁, l₂, f₂, hS⟩ := hS E r s bad K W hK hW
  obtain ⟨T, hT⟩ := hL E m₀ ((-((s : ℝ) / 2) : ℝ) : ℂ) (((r : ℝ) / 2 : ℝ) : ℂ)
  choose J₁ i₁ D₁ C₁ a₁ b₁ using fun p : T => ih₁ K₁ W₁ p.1.1 l₁ f₁
  choose J₂ i₂ D₂ C₂ a₂ b₂ using fun p : T => ih₂ K₂ W₂ p.1.2 l₂ f₂
  have hν := fun x : ℝ => GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) x
  choose D d₁ d₂ d₃ using fun j : Σ p : T, J₁ p × J₂ p => hA E r s (D₁ j.1 j.2.1) (D₂ j.1 j.2.2)
    (GlobalTheory.Mem.Chr.CharModel.absChar E ((-((s : ℝ) / 2) : ℝ) : ℂ)) (GlobalTheory.Mem.Chr.CharModel.absChar E (((r : ℝ) / 2 : ℝ) : ℂ)) hr hs
  refine ⟨Σ p : T, J₁ p × J₂ p, inferInstance, D, _, fun j => ⟨fun π _ => d₁ j π, fun w hw =>
    d₂ j w _ _ ((hν _).1 w) ((hν _).1 w) ((a₁ j.1 j.2.1).2 w hw) ((a₂ j.1 j.2.2).2 w hw)⟩, fun φ m B h hm => ?_⟩
  choose φ₁ φ₂ m₁ m₂ B₁ B₂ e₁ e₂ e₃ e₄ using fun k => hS (φ k) (m k) (B k) (h k).1 (h k).2
  obtain ⟨p, hp, σ, hσ, t₁, t₂⟩ := hT m m₁ m₂ e₃ hm
  obtain ⟨j₁, σ₁, hσ₁, v₁, u₁⟩ := b₁ ⟨p, hp⟩ (fun k => φ₁ (σ k)) _ (fun k => B₁ (σ k)) (fun k => ⟨e₁ _, trivial⟩) t₁
  obtain ⟨j₂, σ₂, hσ₂, v₂, u₂⟩ := b₂ ⟨p, hp⟩ (fun k => φ₂ (σ (σ₁ k))) (fun k => m₂ (σ (σ₁ k))) (fun k => B₂ (σ (σ₁ k)))
    (fun k => ⟨e₂ _, trivial⟩) fun τ ε hε => hσ₁.tendsto_atTop.eventually (t₂ τ ε hε)
  have h₀ : m₀ = fun t => (p.1 t).map (· + ((-((s : ℝ) / 2) : ℝ) : ℂ)) + (p.2 t).map (· + (((r : ℝ) / 2 : ℝ) : ℂ)) := by
    obtain ⟨hu, hsh, hadd⟩ := hM E
    have c₁ := hsh _ _ (fun _ => ((-((s : ℝ) / 2) : ℝ) : ℂ)) _ t₁ tendsto_const_nhds
    have c₂ := hsh _ _ (fun _ => (((r : ℝ) / 2 : ℝ) : ℂ)) _ t₂ tendsto_const_nhds
    have c₃ := hadd _ _ _ _ c₁ c₂
    refine hu (fun k => m (σ k)) _ _ (fun τ ε hε => hσ.tendsto_atTop.eventually (hm τ ε hε)) ?_
    have : (fun k => m (σ k)) = fun k t => (m₁ (σ k) t).map (· + ((-((s : ℝ) / 2) : ℝ) : ℂ)) +
        (m₂ (σ k) t).map (· + (((r : ℝ) / 2 : ℝ) : ℂ)) := by
      funext k t
      exact e₃ _ t
    rw [this]
    exact c₃
  refine ⟨⟨⟨p, hp⟩, j₁, j₂⟩, fun k => σ (σ₁ (σ₂ k)), hσ.comp (hσ₁.comp hσ₂), fun τ => ?_, fun w hw => ?_⟩
  · rw [d₃ ⟨⟨p, hp⟩, j₁, j₂⟩ τ, h₀]
    have key : ∀ (n : ℕ) (D' : CD E n) (z : ℝ) (x : (E →+* ℂ) → Multiset ℂ), D'.Inf x →
        ∑ i, ((D'.P i).twist (GlobalTheory.Mem.Chr.CharModel.absChar E (z : ℂ))).infChar τ = (x τ).map (· + (z : ℂ)) := by
      intro n D' z x hx
      rw [← hx τ]
      simp only [fun i => ((hI E _ (D'.P i) (z : ℂ) τ).2)]
      exact (map_sum (Multiset.mapAddMonoidHom (· + (z : ℂ))) _ _).symm
    exact congrArg₂ (· + ·) (key _ _ _ _ v₁) (key _ _ _ _ v₂)
  have := hC.2 (qV E w) r s _ _ _ _ ((GlobalTheory.Mem.Chr.CharModel.absChar E ((-((s : ℝ) / 2) : ℝ) : ℂ)).val w)
    ((GlobalTheory.Mem.Chr.CharModel.absChar E (((r : ℝ) / 2 : ℝ) : ℂ)).val w) (qV_ne_zero w)
    (fun i => (u₁ w hw i).comp hσ₂.tendsto_atTop) (u₂ w hw)
  intro i
  refine (this i).congr fun k => ?_
  exact congrArg (fun M => satEig (qV E w) (r + s) M i) (e₄ _ _ _ (hν _) (hν _) w hw).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.CuspCaseJ
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula
open PositivityTheory.Rg.Rs.StrStepB
open PositivityTheory.Rg.BcB.SpectralAccumulation (TypeB HasType InfBdd)

private theorem rel_sum {ε : ℝ} {a b : Multiset ℂ} (h : Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) a b) :
    ‖a.sum - b.sum‖ ≤ b.card * ε := by
  induction h with
  | zero => simp
  | @cons x y s t h1 _ ih =>
    rw [Multiset.sum_cons, Multiset.sum_cons, Multiset.card_cons, add_sub_add_comm]
    refine (norm_add_le _ _).trans ?_
    push_cast
    linarith

private theorem sum_to {m : ℕ → Multiset ℂ} {b : Multiset ℂ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) (m k) b) :
    Tendsto (fun k => (m k).sum) atTop (𝓝 b.sum) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hc : (0 : ℝ) < b.card + 1 := by positivity
  filter_upwards [h (ε / (b.card + 1)) (by positivity)] with k hk
  rw [dist_eq_norm]
  refine (rel_sum hk).trans_lt ?_
  rw [mul_div_assoc', div_lt_iff₀ hc]
  linarith

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.cuspCaseJ :
    CuspMem → CuspFin → NormTw → NormUniq → SatComb → AbsInf → MToLaws → CuspCaseJ := by
  intro hM hF hN hU hC hA hL E _ _ _ N h1 bad K W m₀ X hb hK hW hX
  classical
  set c : ℂ := (N : ℂ) * (Fintype.card (E →+* ℂ) : ℂ) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  set z₀ : ℂ := (∑ t, (m₀ t).sum) / c
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ t, ∀ x ∈ m₀ t, ‖x‖ ≤ R :=
    ⟨∑ t, ((m₀ t).map (‖·‖)).sum, fun t x hx => (Multiset.single_le_sum (by simp) _ (Multiset.mem_map_of_mem _ hx)).trans
      (Finset.single_le_sum (f := fun t => ((m₀ t).map (‖·‖)).sum) (fun _ _ => Multiset.sum_nonneg (by simp)) (Finset.mem_univ t))⟩
  have hfin := (hF E N h1 K W (R + 1 + (‖z₀‖ + 1)) hK.isOpen hW).subset
    (t := {π | (GlobalTheory.DiscSpec.IsNormalised π ∧ HasType K W π.V ∧ InfBdd (R + 1 + (‖z₀‖ + 1)) π.V) ∧ π ∉ X ∧
      ∀ w ∉ bad, ∃ C, (CG.mk π).HasSat w C}) fun _ h => h.1
  have hC₀ : ∀ (j : hfin.toFinset) w, ∃ C, w ∉ bad → (CG.mk j.1).HasSat w C := fun j w => by
    by_cases hw : w ∈ bad
    · exact ⟨0, fun h => (h hw).elim⟩
    · exact ((hfin.mem_toFinset.1 j.2).2.2 w hw).imp fun _ h _ => h
  choose C₀ hC₀ using hC₀
  refine ⟨hfin.toFinset, inferInstance, fun j => ⟨1, fun _ => N, fun _ => (CG.mk j.1).twist (Model.absC E z₀), fun _ => h1, by simp⟩,
    fun j w => (C₀ j w).map (· * (Model.absC E z₀).val w), fun j => ⟨fun π hπ hh => ?_, fun w hw =>
      ⟨fun _ => _, fun _ => PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ (absC_unrAt _ w) (hC₀ j w hw), by simp⟩⟩, fun φ m B h hm => ?_⟩
  · obtain ⟨i, hi⟩ := hh
    have hj := hfin.mem_toFinset.1 j.2
    have e := hU E N h1 π j.1 z₀ (hX π hπ) hj.1.1 (by rw [← CG.twist_mk]; exact eq_of_heq (Sigma.mk.inj hi).2)
    exact hj.2.1 (e ▸ hπ)
  choose π p₁ p₂ p₃ using fun k => hM E N h1 bad hb K W (φ k) (m k) (B k) (h k).1 (h k).2.1
  choose π₀ z q₁ q₂ q₃ q₄ q₅ q₆ using fun k => hN E N h1 bad K W hK (π k) (φ k) (m k) (p₁ k) (h k).1.ne (h k).1.ty (p₂ k)
  have hz : Tendsto z atTop (𝓝 z₀) := by
    refine ((tendsto_finsetSum _ fun t _ => sum_to (hm t)).div_const c).congr fun k => ?_
    rw [q₅ k, mul_div_cancel_left₀ _ hc0]
  have hs : ∀ k, ∀ w ∉ bad, (CG.mk (π₀ k)).HasSat w ((B k w).map (· * (Model.absC E (-z k)).val w)) := fun k w hw => by
    have := PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ (absC_unrAt (-z k) w) (p₃ k w hw)
    rwa [q₂ k, ← CG.twist_mk, ← CG.twist_mul, ← absC_add, add_neg_cancel, absC_zero, CG.twist_one] at this
  have hev : ∀ᶠ k in atTop, π₀ k ∈ hfin.toFinset := by
    filter_upwards [eventually_all.2 fun t => hm t 1 one_pos, Metric.tendsto_nhds.1 hz 1 one_pos] with k k₁ k₂
    refine hfin.mem_toFinset.2 ⟨⟨q₁ k, q₃ k, fun t => ⟨_, q₄ k t, fun x hx => ?_⟩⟩, fun hx => ?_, fun w hw => ⟨_, hs k w hw⟩⟩
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      obtain ⟨y₀, hy₀, h2⟩ := Multiset.exists_mem_of_rel_of_mem (k₁ t) hy
      have h3 := hR t y₀ hy₀
      have h4 := norm_sub_norm_le y y₀
      have h5 := norm_sub_norm_le (z k) z₀
      rw [dist_eq_norm] at k₂
      have h6 := norm_sub_le y (z k)
      linarith
    · obtain ⟨ψ, hψ, z', e⟩ := q₆ k
      exact (h k).2.2 _ hx ψ hψ z' e
  obtain ⟨j, hj⟩ : ∃ j : hfin.toFinset, ∃ᶠ k in atTop, π₀ k = j.1 := by
    by_contra hn
    push Not at hn
    obtain ⟨k, k₁, k₂⟩ := (hev.and (eventually_all.2 hn)).exists
    exact k₂ ⟨_, k₁⟩ rfl
  obtain ⟨σ, hσ, e⟩ := extraction_of_frequently_atTop hj
  obtain ⟨hLu, hLs, -⟩ := hL E
  have hk : ∀ k t, (m (σ k) t).map (· + -z (σ k)) = (CG.mk j.1).infChar t := fun k t => by
    have h2 := q₄ (σ k) t
    rw [e k] at h2
    have h3 := CG.HasInfChar.infChar_eq (π := CG.mk j.1) h2
    simpa [sub_eq_add_neg] using h3.symm
  have hm' : MTo (fun k => m (σ k)) m₀ := fun t ε hε => hσ.tendsto_atTop.eventually (hm t ε hε)
  have hs₁ := hLs _ _ (fun k => -z (σ k)) (-z₀) hm' (hz.comp hσ.tendsto_atTop).neg
  have hs₂ : MTo (fun k t => (m (σ k) t).map (· + -z (σ k))) fun t => (CG.mk j.1).infChar t := fun t ε hε =>
    Eventually.of_forall fun k => by
      show Multiset.Rel _ ((m (σ k) t).map (· + -z (σ k))) ((CG.mk j.1).infChar t)
      rw [hk k t]
      exact Multiset.rel_refl_of_refl_on fun x _ => by simpa using hε.le
  have hu := hLu _ _ _ hs₂ hs₁
  refine ⟨j, σ, hσ, fun τ => ?_, fun w hw i => ?_⟩
  · have h2 := (hA E N (CG.mk j.1) z₀ τ).1
    have h3 : (CG.mk j.1).infChar τ = (m₀ τ).map (· + -z₀) := congrFun hu τ
    rw [h3] at h2
    simpa [Multiset.map_map, Function.comp_def, CD.Inf] using h2
  have hv : Tendsto (fun k => (((Model.absC E (z (σ k))).val w : ℂˣ) : ℂ)) atTop (𝓝 (((Model.absC E z₀).val w : ℂˣ) : ℂ)) := by
    simp only [absC_val]
    exact (hz.comp hσ.tendsto_atTop).neg.const_cpow (Or.inl (Nat.cast_ne_zero.2 (by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot)))
  refine (hC.1 (qV E w) N (C₀ j w) _ _ hv i).congr fun k => ?_
  have h2 := p₃ (σ k) w hw
  rw [q₂, e k, ← CG.twist_mk] at h2
  exact congrArg (fun M => satEig (qV E w) N M i)
    ((PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ (absC_unrAt _ w) (hC₀ j w hw)).unique h2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.CuspReadIOf
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula
open GroundTheory.Automorphic.AutomorphicForm (constantTerm)

private theorem readJ_or {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} {bad : Set (UpperTheory.V.Cj.S.Pl E)} {K W m₀}
    {X : Set (CuspSub E N)} {ι : Type} [Fintype ι] {P : ι → Sm E N → Prop} {Q : Sm E N → Prop}
    (h : ∀ i, ReadJ bad K W m₀ X (P i)) (hQ : ∀ φ, IsAutForm φ → Q φ → ∃ i, P i φ) : ReadJ bad K W m₀ X Q := by
  choose J i D C a b using h
  refine ⟨Σ i, J i, inferInstance, fun j => D j.1 j.2, fun j => C j.1 j.2, fun j => a j.1 j.2, fun φ m B h hm => ?_⟩
  choose c hc using fun k => hQ (φ k) (h k).1.aut (h k).2
  obtain ⟨i₀, h0⟩ := Finite.exists_infinite_fiber c
  have h1 : ∃ᶠ k in atTop, c k = i₀ := Nat.frequently_atTop_iff_infinite.2 (Set.infinite_coe_iff.1 h0)
  obtain ⟨σ, hσ, e⟩ := extraction_of_frequently_atTop h1
  obtain ⟨j, s, hs, hI, u⟩ := b i₀ (fun k => φ (σ k)) (fun k => m (σ k)) (fun k => B (σ k)) (fun k => ⟨(h _).1, e k ▸ hc _⟩)
    fun τ ε hε => hσ.tendsto_atTop.eventually (hm τ ε hε)
  exact ⟨⟨i₀, j⟩, fun k => σ (s k), hσ.comp hs, hI, u⟩

private theorem readJ_all (hC : CuspCaseJ) (hT : CtCaseJ) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {bad : Set (UpperTheory.V.Cj.S.Pl E)} (hb : bad.Finite) (N : ℕ) : ∀ K (W : Submodule ℂ (Kinf E N → ℂ)) m₀ (X : Set (CuspSub E N)),
    Lev bad K → FiniteDimensional ℂ W → (∀ π ∈ X, ∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E N t * g) = ψ.1 g) →
    ReadJ bad K W m₀ X (Excl X) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro K W m₀ X hK hW hX
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨Unit, inferInstance, fun _ => CD.nil E, fun _ _ => 0, fun _ => ⟨fun π _ ⟨i, _⟩ => i.elim0,
      fun w _ => ⟨fun i => i.elim0, fun i => i.elim0, rfl⟩⟩, fun φ m B h hm => ⟨(), id, strictMono_id, ?_, fun w hw i => ?_⟩⟩
    · have e0 : m₀ = fun _ => 0 := by
        funext τ
        obtain ⟨k, hk⟩ := (hm τ 1 one_pos).exists
        have hc := Multiset.card_eq_card_of_rel hk
        rw [((h k).1.cap τ).1] at hc
        exact Multiset.card_eq_zero.1 hc.symm
      rw [e0]
      exact fun _ => rfl
    · have e : ∀ k, B k w = 0 := fun k => Multiset.card_eq_zero.1 ((h k).1.sat w hw).2.2.1
      simp only [e]
      exact tendsto_const_nhds
  have ih' : ∀ M < N, ∀ K (W : Submodule ℂ (Kinf E M → ℂ)) m₀, Lev bad K → FiniteDimensional ℂ W →
      ReadJ (N := M) bad K W m₀ ∅ fun _ => True := fun M hM K W m₀ hK hW =>
    readJ_or (ι := Unit) (fun _ => ih M hM K W m₀ ∅ hK hW fun _ h => h.elim) fun _ _ _ => ⟨(), fun _ h => h.elim⟩
  refine readJ_or (ι := Option {r : Fin N // 0 < r.1})
    (P := fun o φ => o.elim (IsCuspForm φ ∧ Excl X φ) fun r => ∃ g, constantTerm r.1.1 φ.1 g ≠ 0) ?_ fun φ ha hx => ?_
  · rintro (_ | ⟨⟨r, hr⟩, h0⟩)
    · exact hC E N hN bad K W m₀ X hb hK hW hX
    · obtain ⟨s, rfl⟩ : ∃ s, N = r + s := ⟨N - r, by omega⟩
      have h0' : 0 < r := h0
      exact hT E r s h0' (by omega) bad (ih' r hr) (ih' s (by omega)) K W m₀ X hK hW
  · by_cases hc : IsCuspForm φ
    · exact ⟨none, hc, hx⟩
    · have h1 : ¬ GroundTheory.Automorphic.AutomorphicForm.IsCuspidal φ.1 := fun h2 =>
        hc ((UpperTheory.V.Cm.isCuspForm_iff φ).2 ⟨(UpperTheory.V.Cm.isAutForm_iff φ).1 ha, h2⟩)
      unfold GroundTheory.Automorphic.AutomorphicForm.IsCuspidal at h1
      push Not at h1
      obtain ⟨r, h0, hr, hg⟩ := h1
      exact ⟨some ⟨⟨r, hr⟩, h0⟩, hg⟩

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.cuspReadI_of :
    LevShrink → CuspCaseJ → CtCaseJ → CuspReadI := by
  intro hL hC hT E _ _ _ N K W bad m₀ X ho hW hb hl _ hX
  obtain ⟨K', hle, hK', -⟩ := hL E N bad K ho hl
  obtain ⟨J, i, D, C, a, b⟩ := readJ_all hC hT hb N K' W m₀ X hK' hW hX
  classical
  refine ⟨{j : J // (D j).Inf m₀}, inferInstance, fun j => D j.1, fun j => C j.1, fun j => a j.1, fun j => j.2,
    fun φ m B h hm => ?_⟩
  obtain ⟨j, s, hs, hI, u⟩ := b φ m B (fun k =>
    ⟨⟨(h k).1, (h k).2.1, ⟨fun u hu => (h k).2.2.1.1 u (hle hu), (h k).2.2.1.2⟩, (h k).2.2.2.1, (h k).2.2.2.2.1⟩,
      (h k).2.2.2.2.2⟩) hm
  exact ⟨⟨j, hI⟩, s, hs, u⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DualWt
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.dualWt :
    DualWt := fun _ lam => ⟨lam.dual, GlobalTheory.DefiniteBC.infOfWeight_dual lam⟩
end

