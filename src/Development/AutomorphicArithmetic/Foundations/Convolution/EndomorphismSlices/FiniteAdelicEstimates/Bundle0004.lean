module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PInfConv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocOk
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OrthogonalKeepingHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbAlg

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.InfLimit
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem zVal_ite' {m : ℕ} (c : Prop) [Decidable c] (L : List (Bool × ℕ)) (χ : Inf m) :
    zVal (if c then L else []) χ = if c then zVal L χ else 1 := by
  split_ifs
  · rfl
  · simp [zVal]

private theorem zVal_one' {m : ℕ} (r : Bool) (k : ℕ) (χ : Inf m) :
    zVal [(r, k)] χ = GlobalTheory.Dec.gelfVal (χ r) k := by
  simp [zVal]

theorem infLimit : InfLimit := by
  intro E _ _ _ a b l₁ l₂ D A S Z L T e₁ e₂ s sk χa χb hs hsk ha hb
  obtain ⟨-, -, -, hone, hpt⟩ := ptOk E a b l₁ l₂ D A
  have h0 : s (.inl ()) = 1 := by
    rw [hs (.inl ()) trivial]
    exact hone _
  have hv₁ : ∀ v r m, s (.inr (.inl (v, r, m, false))) = GlobalTheory.Dec.gelfVal (chi l₁ v r) m := by
    intro v r m
    rw [hs (.inr (.inl (v, r, m, false))) trivial]
    show (A.pt _ _ (A.idm S L)).val _ _ = _
    rw [hpt, hone]
    simp only [zVal_ite']
    simp [zVal_one']
  have hv₂ : ∀ v r m, s (.inr (.inl (v, r, m, true))) = GlobalTheory.Dec.gelfVal (chi l₂ v r) m := by
    intro v r m
    rw [hs (.inr (.inl (v, r, m, true))) trivial]
    show (A.pt _ _ (A.idm S L)).val _ _ = _
    rw [hpt, hone]
    simp only [zVal_ite']
    simp [zVal_one']
  have hne : s (.inl ()) ≠ 0 := by rw [h0]; exact one_ne_zero
  have hc₁ : ∀ v r m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χa k v r) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (chi l₁ v r) m)) := by
    intro v r m
    have h := (hsk (.inr (.inl (v, r, m, false)))).div (hsk (.inl ())) hne
    rw [h0, div_one, hv₁] at h
    exact h.congr fun k => (ha k v r m).symm
  have hc₂ : ∀ v r m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χb k v r) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (chi l₂ v r) m)) := by
    intro v r m
    have h := (hsk (.inr (.inl (v, r, m, true)))).div (hsk (.inl ())) hne
    rw [h0, div_one, hv₂] at h
    exact h.congr fun k => (hb k v r m).symm
  refine ⟨h0, fun τ ε hε => ?_, fun τ ε hε => ?_⟩
  · exact infConv a (fun k => χa k (InfinitePlace.mk τ) _) (chi l₁ (InfinitePlace.mk τ) _) (hc₁ _ _) ε hε
  · exact infConv b (fun k => χb k (InfinitePlace.mk τ) _) (chi l₂ (InfinitePlace.mk τ) _) (hc₂ _ _) ε hε

end UpperTheory.Zero.ConvolutionTheory.EB

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem levelFam_of {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (Z : Finset (Pl E))
    (K : ∀ w : Pl E, Subgroup (GLw n w)) (hZ : ∀ w ∈ Z, IsSplitAt w) (ho : ∀ w, IsOpen (K w : Set (GLw n w)))
    (hle : ∀ w, K w ≤ GlobalTheory.LFun.KGL w (n := n)) (hoff : ∀ w ∉ Z, K w = GlobalTheory.LFun.KGL w (n := n)) :
    IsLevelFam (GlobalTheory.BCT.thL n) (fun w : Pl E => GlobalTheory.LFun.KGL w (n := n)) K := by
  refine ⟨fun w => ?_, ?_⟩
  · by_cases hw : w ∈ Z
    · refine ⟨ho w, hle w, fun k hk => ?_⟩
      have h : GlobalTheory.BCT.thL n w = MonoidHom.id _ := by
        unfold GlobalTheory.BCT.thL
        rw [if_pos (hZ w hw)]
      rw [h]
      exact hk
    · rw [hoff w hw]
      exact PositivityTheory.Rg.BcB.F.LocOk.lev_K n w
  · filter_upwards [Z.finite_toSet.compl_mem_cofinite] with w hw
    exact hoff w hw

theorem positionTest : PositionTest := by
  intro E _ _ _ a b S Z L hS
  have hZ : ∀ w ∈ Z, IsSplitAt w := fun w hw => (hS w hw).2
  have h₁ := levelFam_of Z L.L₁ hZ L.open₁ L.le₁ fun w hw => (L.off w hw).1
  have h₂ := levelFam_of Z L.L₂ hZ L.open₂ L.le₂ fun w hw => (L.off w hw).2
  have hH : ∀ w, IsHecke ((L.L₁ w).prod (L.L₂ w)) (L.ln w) := fun w => (locAlg E a b Z L w).1
  have hI : ∀ w ∉ Z, L.ln w = (K2 a b w : Set _).indicator 1 := fun w hw => (locAlg E a b Z L w).2.2.1 hw
  have hK : ∀ w ∉ Z, (L.L₁ w).prod (L.L₂ w) = K2 a b w := by
    intro w hw
    rw [(L.off w hw).1, (L.off w hw).2]
  refine ⟨fun w _ => hH w, ⟨L.L₁, L.L₂, h₁, h₂, hH, ?_⟩, fun φ hφ => ⟨fun w hw => ?_, fun T e =>
    ⟨L.L₁, L.L₂, h₁, h₂, fun w => ?_, ?_⟩⟩⟩
  · filter_upwards [Z.finite_toSet.compl_mem_cofinite] with w hw
    exact hI w hw
  · have h := PositivityTheory.Rg.BcB.F.LocOk.prod_open_le (h₁.1 w) (h₂.1 w)
    exact ⟨_, h.1, h.2, hφ w hw⟩
  · by_cases hw : w ∈ Z
    · have h : intersection_update_fsHerm_neg_one Z T φ e w = φ w := if_pos hw
      rw [h]
      exact hφ w hw
    · by_cases hT : w ∈ T
      · have h : intersection_update_fsHerm_neg_one Z T φ e w = fn2 a b w (e w) := by
          unfold intersection_update_fsHerm_neg_one
          rw [if_neg hw, if_pos hT]
        rw [h]
        show GlobalTheory.BCT.IsHecke ((L.L₁ w).prod (L.L₂ w)) _
        rw [hK w hw]
        exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w (e w)
      · have h : intersection_update_fsHerm_neg_one Z T φ e w = L.ln w := by
          unfold intersection_update_fsHerm_neg_one
          rw [if_neg hw, if_neg hT, hI w hw]
        rw [h]
        exact hH w
  · filter_upwards [(Z ∪ T).finite_toSet.compl_mem_cofinite] with w hw
    have hw' : w ∉ Z ∧ w ∉ T := by simpa using hw
    unfold intersection_update_fsHerm_neg_one
    rw [if_neg hw'.1, if_neg hw'.2]

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RealAlg
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem conv_smul' {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {ι : Type} [Fintype ι]
    (μ : Measure (H E a b)) (Φ : Matrix ι ι (H E a b → ℂ)) (c : ℂ) (f : ι → H E a b → ℂ) :
    PositivityTheory.Rg.BcB.E.conv μ Φ (c • f) = c • PositivityTheory.Rg.BcB.E.conv μ Φ f := by
  funext i x
  simp only [PositivityTheory.Rg.BcB.E.conv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

set_option maxHeartbeats 1000000 in
theorem realAlg : RealAlg := by
  intro E _ _ _ B Q _ Γ _ t v 𝔄 a₀ g s hok hK hT hs hs0
  let gg : Γ → BGen B := fun x => Sum.inr (t x)
  let X : B.Hb →L[ℂ] B.Hb := (t a₀).op
  have hmem : ∀ y : 𝔄.B, 𝔄.F y ∈ StarAlgebra.adjoin ℂ (Rd.gOps gg ∪ {X}) := by
    have hle : StarAlgebra.adjoin ℂ (Set.range 𝔄.ι) ≤ (StarAlgebra.adjoin ℂ (Rd.gOps gg ∪ {X})).comap 𝔄.F := by
      refine StarAlgebra.adjoin_le ?_
      rintro _ ⟨x, rfl⟩
      show 𝔄.F (𝔄.ι x) ∈ StarAlgebra.adjoin ℂ (Rd.gOps gg ∪ {X})
      rw [𝔄.hF]
      exact StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)
    intro y
    have hy : y ∈ StarAlgebra.adjoin ℂ (Set.range 𝔄.ι) := by
      rw [𝔄.top]
      exact StarSubalgebra.mem_top
    exact hle hy
  have hΦ : ∀ y : 𝔄.B, ∃ Φ : Matrix B.I B.I (H E B.a B.b → ℂ), IsTestM Φ ∧ IsROp B.D Φ (𝔄.F y * (t a₀).op) := fun y =>
    Rd.phiEx BlockFiniteConvolution.blkOp₀ BlockFiniteConvolution.blkWord₀ blkSum adjWords gg X (t a₀) (t a₀) (fun x => hok x) (hok a₀) rfl (hok a₀)
      ⟨𝔄.F y, hmem y⟩
  choose Φ hΦt hΦr using hΦ
  have hop : ∀ y : 𝔄.B, ∃ T : B.Hb →L[ℂ] B.Hb, IsROp B.D (Φ y) T ∧
      (∀ w : Q, T (Q.subtypeL w) = Q.subtypeL (𝔄.R (y * 𝔄.ι a₀) w)) ∧
      ∀ u, (∀ w : Q, inner ℂ (Q.subtypeL w) u = 0) → ∀ w : Q, inner ℂ (Q.subtypeL w) (T u) = 0 := by
    intro y
    have hTy : 𝔄.F y * (t a₀).op = 𝔄.F (y * 𝔄.ι a₀) := by rw [map_mul, 𝔄.hF]
    refine ⟨_, hΦr y, fun w => ?_, fun u hu w => ?_⟩
    · rw [hTy]
      exact (𝔄.hR _ w).symm
    · rw [hTy]
      have h1 : (ContinuousLinearMap.adjoint (𝔄.F (y * 𝔄.ι a₀))) (w : B.Hb) =
          Q.subtypeL (𝔄.R (star (y * 𝔄.ι a₀)) w) := by
        rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
        exact (𝔄.hR _ w).symm
      have h2 := hu (𝔄.R (star (y * 𝔄.ι a₀)) w)
      rw [← h1, ContinuousLinearMap.adjoint_inner_left] at h2
      exact h2
  have hC : ({1} ∪ Set.range 𝔄.ι : Set 𝔄.B).Countable :=
    (Set.countable_singleton _).union (Set.countable_range _)
  obtain ⟨M, sk, f, hlim, hk⟩ := PositivityTheory.Rg.BcB.E2.orthogonal_keeping_holds E B.a B.b B.D B.I Q Q.subtypeL (fun w => rfl) 𝔄.B 𝔄.R s
    (𝔄.ι a₀) ({1} ∪ Set.range 𝔄.ι) Φ g hs hs0 hC (Or.inl rfl) hΦt hop
    (fun j w => (Submodule.mem_orthogonal _ _).1 (hT.1 j) w w.2) hT.2
  refine ⟨fun k x => sk k (𝔄.ι x), f, fun x => hlim _ (Or.inr ⟨x, rfl⟩), fun k => ?_⟩
  obtain ⟨h0, hc, hne, hL, hW, hconv, horth⟩ := hk k
  have hO := fun x => BlockFiniteConvolution.blkOp₀ E B (t x) (t a₀) (hok x) (hok a₀)
  have ha : PositivityTheory.Rg.BcB.E.conv B.D.μ (t a₀).Φ (f k) = sk k (𝔄.ι a₀) • f k := by
    have h1 := hconv 1 (Or.inl rfl)
    rw [one_mul] at h1
    rw [← h1]
    refine PositivityTheory.Rg.BcB.E2.conv_eq_of_isROp B.D (hO a₀).1 (hΦt 1) ?_ (hΦr 1) hc hL
    rw [map_one, one_mul]
    exact (hO a₀).2.1
  have hx : ∀ x, PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ (f k) = sk k (𝔄.ι x) • f k := by
    intro x
    have h1 := hconv (𝔄.ι x) (Or.inr ⟨x, rfl⟩)
    have hok' := (hO x).2.2.1
    have hm := BlockFiniteConvolution.blkOp₀ E B _ _ hok' hok'
    have h2 : PositivityTheory.Rg.BcB.E.conv B.D.μ ((t x).mul (t a₀)).Φ (f k) = PositivityTheory.Rg.BcB.E.conv B.D.μ (Φ (𝔄.ι x)) (f k) := by
      refine PositivityTheory.Rg.BcB.E2.conv_eq_of_isROp B.D hm.1 (hΦt _) ?_ (hΦr _) hc hL
      rw [𝔄.hF, ← (hO x).2.2.2.1]
      exact hm.2.1
    have h3 := (UpperTheory.Zero.ConvolutionTheory.EB.convMul E B (f k) hc).1 (t x) (t a₀) (hok x) (hok a₀)
    rw [ha, conv_smul', h2, h1, map_mul] at h3
    calc PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ (f k)
        = (sk k (𝔄.ι a₀))⁻¹ • (sk k (𝔄.ι a₀)) • PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ (f k) := (inv_smul_smul₀ h0 _).symm
      _ = (sk k (𝔄.ι a₀))⁻¹ • ((sk k (𝔄.ι x) * sk k (𝔄.ι a₀)) • f k) := by rw [← h3]
      _ = sk k (𝔄.ι x) • f k := by
        rw [smul_smul]
        congr 1
        field_simp
  exact ⟨h0, ⟨hc, hne, hL, ⟨M, hW⟩, hx⟩, horth⟩

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.WordRep
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem rep_sum {B : Block E} {χa : InfinitePlace E → Inf B.a} {χb : InfinitePlace E → Inf B.b}
    {ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)} {J : Type} [Fintype J] (c v : J → ℂ)
    (U : J → (B.Hb →L[ℂ] B.Hb)) (R : J → ℝ) (hR : ∀ j, 0 ≤ R j)
    (h : ∀ j, Rep B χa χb ψ (v j) (R j) (U j)) :
    Rep B χa χb ψ (∑ j, c j * v j) (∑ j, R j) (∑ j, c j • U j) := by
  choose C hC hv hU using h
  refine ⟨⟨Σ j, (C j).J, Finset.univ.sigma fun j => (C j).s, fun p => c p.1 * (C p.1).c p.2,
    fun p => (C p.1).t p.2⟩, ?_, ?_, ?_⟩
  · rintro ⟨j, i⟩ hi
    have hi' : i ∈ (C j).s := (Finset.mem_sigma.1 hi).2
    obtain ⟨h1, h2, h3, h4⟩ := hC j i hi'
    have hle : R j ≤ ∑ k, R k := Finset.single_le_sum (fun k _ => hR k) (Finset.mem_univ j)
    exact ⟨h1, h2, h3.trans hle, h4.trans hle⟩
  · simp only [Cmb.val]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hv j]
    simp only [Cmb.val, Finset.mul_sum, mul_assoc]
  · simp only [Cmb.op]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hU j]
    simp only [Cmb.op, Finset.smul_sum, mul_smul]

private theorem rep_word {B : Block E} {χa : InfinitePlace E → Inf B.a} {χb : InfinitePlace E → Inf B.b}
    (hA : ∀ v, IsHerm (χa v)) (hB : ∀ v, IsHerm (χb v)) {Γ : Type} (t : Γ → PT B) (t₀ : PT B) (h₀ : t₀.Ok)
    (ht : ∀ x, (t x).Ok ∧ (t x).ψ = t₀.ψ) (hm : mulF B.ν t₀.ψ t₀.ψ = t₀.ψ) (ha : adjF t₀.ψ = t₀.ψ)
    (w : List (Γ × Bool)) :
    ∃ R, 0 ≤ R ∧ Rep B χa χb t₀.ψ (wdVal (fun x => (t x).val χa χb) w * t₀.val χa χb) R
      (wdVal (fun x => (t x).op) w * t₀.op) := by
  obtain ⟨-, hp, -, hmul⟩ := repAlg E B χa χb
  induction w with
  | nil => exact ⟨max t₀.T t₀.r, le_max_of_le_left h₀.T, by simpa [wdVal] using hp t₀ h₀⟩
  | cons p w ih =>
    obtain ⟨R, hR, hrep⟩ := ih
    obtain ⟨x, b⟩ := p
    obtain ⟨hx, hψ⟩ := ht x
    obtain ⟨-, -, -, -, hadjOk, hadjOp, -, hadjVal⟩ :=
      PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.blkOp₀ E B (t x) (t x) hx hx
    have key : ∃ R', 0 ≤ R' ∧ Rep B χa χb t₀.ψ (if b then star ((t x).val χa χb) else (t x).val χa χb) R'
        (if b then star (t x).op else (t x).op) := by
      cases b
      · refine ⟨max (t x).T (t x).r, le_max_of_le_left hx.T, ?_⟩
        have h1 := hp (t x) hx
        rw [hψ] at h1
        simpa using h1
      · refine ⟨max (t x).adj.T (t x).adj.r, le_max_of_le_left hadjOk.T, ?_⟩
        have h1 := hp _ hadjOk
        have e : (t x).adj.ψ = t₀.ψ := by
          change adjF (t x).ψ = _
          rw [hψ, ha]
        rw [hadjOp, hadjVal χa χb hA hB, e] at h1
        simpa [ContinuousLinearMap.star_eq_adjoint] using h1
    obtain ⟨R', hR', hl⟩ := key
    refine ⟨R' + R + B.c, add_nonneg (add_nonneg hR' hR) B.c_nonneg, ?_⟩
    have h2 := hmul _ _ _ _ _ _ _ _ hl hrep
    rw [hm] at h2
    have e1 : ∀ {A : Type} [Monoid A] [Star A] (g : Γ → A), wdVal g ((x, b) :: w) =
        (if b then star (g x) else g x) * wdVal g w := fun g => by simp [wdVal]
    rw [e1, e1, mul_assoc, mul_assoc]
    exact h2

theorem wordRep : WordRep := by
  intro E _ _ _ B χa χb Γ t t₀ J _ c w hA hB h₀ ht hm ha
  choose R hR hrep using fun j => rep_word hA hB t t₀ h₀ ht hm ha (w j)
  refine ⟨∑ j, R j, Finset.sum_nonneg fun j _ => hR j, ?_⟩
  have h1 := rep_sum c _ _ R hR hrep
  rw [Finset.sum_mul, Finset.sum_mul]
  simpa only [mul_assoc, smul_mul_assoc] using h1

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

