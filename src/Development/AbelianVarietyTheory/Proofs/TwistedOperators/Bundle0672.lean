module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPointBesselStaircaseLatticeFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFrameOddLatticeLeft
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0474

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestMemLatticeStabilizerOfLocalMatrices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.LatOfHasLoc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


set_option maxHeartbeats 800000 in
theorem mem_latGrp_of_hasLoc : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t, ∀ j, 1 ≤ j → ∀ (hj : j ≤ D.R.m)
    (x : GA D (ch.G.V (.grid D.R.m j)))
    (g : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1)),
    HasLoc t ch.S.B hj x g → (∀ w, g w ∈ givenLevel ch.G t w.1 (D.R.m, j)) → x ∈ latGrp ch.G j := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  intro t j h1 hj x g hx hg
  obtain ⟨e, he, hsupp, hloc⟩ := hx
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have e0 : infPart D e = 0 := (GlobalTheory.FunObj.Comparison₂.cpt_idemSum he).1
  have e0' : infPart D (cA D e) = 0 := GlobalTheory.PlaceDatum.infPart_cA e0
  refine ⟨GlobalTheory.LevelCut.mem_GfC_of _ x fun i k => ?_, ?_⟩
  · rw [← hsupp i k, map_mul, map_add (f := _), e0, e0', add_zero, zero_mul]
  · have hl : ∀ (w : Pl D.host.E) (X : ℕ × ℕ), 1 ≤ X.1 → 1 ≤ X.2 →
        givenLevel ch.G t w X = GlobalTheory.SplitWeil.KO (Kw w) _ := by
      rintro w ⟨_ | a, _ | b⟩ h h'
      · omega
      · simp at h
      · simp at h'
      · rfl
    have hβ : IsFrame (ch.S.B.β D.R.m j) (ch.G.Λ (.grid D.R.m j)) := ch.S.B.isFrame_β hS.core.lev le_rfl hj
    have hsd : IsSelfDualC _ (ch.G.Λ (.grid D.R.m j)) :=
      (ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ fun k h => by
        have := (Node.grid.inj h).1; omega).sd
    set c : Lev.EAf D := toEAf D (e + cA D e) with hc
    have hX : (Lev.finE (ch.G.V (.grid D.R.m j)) x).val =
        c • (Lev.finE (ch.G.V (.grid D.R.m j)) x).val + (1 - c) • (1 : Matrix _ _ (Lev.EAf D)) := by
      have hM : (Lev.finE (ch.G.V (.grid D.R.m j)) x).val = (mt _ x).map (toEAf D) := rfl
      rw [hM]
      ext i k
      have h0 := congrArg (toEAf D) (hsupp i k)
      rw [map_mul, Matrix.sub_apply, map_sub] at h0
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
      by_cases hik : i = k
      · subst hik
        simp only [Matrix.one_apply_eq, map_one] at h0 ⊢
        rw [← hc] at h0
        linear_combination -h0
      · simp only [Matrix.one_apply_ne hik, map_zero, sub_zero, mul_zero, add_zero] at h0 ⊢
        exact h0.symm
    have key := GlobalTheory.FunObj.LevRowSucc.prodLev_inf_UA (V := ch.G.V (.grid D.R.m j)) (Λ := ch.G.Λ (.grid D.R.m j))
      (β := ch.S.B.β D.R.m j) hβ hsd (locPl ch.G t) (n' := fun w => (locGrid ch.G t w.1).rank (D.R.m, j))
      (fun w => rank_vertex ch.G t w.1 (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (fun w => GlobalTheory.SplitWeil.KO (Kw w.1) _) fun _ => rfl
    have hmax : Lev.finE (ch.G.V (.grid D.R.m j)) x ∈ ch.G.levMax (.grid D.R.m j) := by
      rw [GridData.levMax, ← key]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => ?_,
        Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun hw' => ?_⟩, GlobalTheory.LevSplit.finE_mem_UA _ x⟩
      · rw [Subgroup.mem_comap, hloc w]
        have := hg w
        rw [hl w.1 (D.R.m, j) hm h1] at this
        exact this
      · rw [Subgroup.mem_comap, (GlobalTheory.OffPartLattice.inBasis_mix (ch.S.B.β D.R.m j) _ _ c hX w').1
          (GlobalTheory.OffPartLattice.cpt_pair_zero (ch.G.V (.grid D.R.m j)) he w' hw')]
        exact one_mem _
    exact hmax

end GlobalTheory.LatOfHasLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitLocalFrameOddLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.AscFin.FrameBF

theorem frame_bf : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank))
    (ι ι' : Fin (σ + 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) (s t : Fin (σ + 1) → k),
  p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  Function.Injective ι ∧ Function.Injective ι' ∧ (∀ a b, ι' b ≠ ι a) ∧
  (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) = Pi.single (ι q) 1) ∧
  (∀ q, t q • ((fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) ᵥ*
    ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (ι' q) 1) ∧
  ∀ a ∈ (pcBF W F (σ + 1) h).A₁,
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = s q * (β.b' *ᵥ fun j => p.pr (a j q)) i) ∧
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ*
      ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) i) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h v hv
  obtain ⟨k, i1, i2, i3, i4, p, β, ϖ, κ, h1, h2, h3, h4, h5, h6, h7⟩ := _root_.GlobalTheory.StairFrame.frame_shape D hq T L μ0 hL sc G W M hM F hF σ h v hv
  obtain ⟨s, t, hs, ht⟩ := _root_.GlobalTheory.FrameZero.xclauses D hq T L μ0 hL sc G W M hM F hF σ h v hv k p β ϖ κ h1 h2 h3 h4 h5 h6 h7
  refine ⟨k, i1, i2, i3, i4, p, β, fun q => κ ⟨q.1, by omega⟩, fun q => κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩, s, t,
    h1, h2, h3, ?_, ?_, ?_, hs, ht, fun a ha =>
      ⟨_root_.GlobalTheory.AscFin.DepthColumn.scaled_column_mem D hq T L μ0 hL sc G W M hM F hF σ h v hv k p β ϖ κ h1 h2 h3 h4 h5 h6 h7 s hs a ha,
       GlobalTheory.T.split_frame_odd_lattice_right D hq T L μ0 hL sc G W M hM F hF σ h v hv k p β ϖ κ h1 h2 h3 h4 h5 h6 h7 t ht a ha⟩⟩
  · intro a b e
    exact Fin.ext (Fin.mk.inj (h5 e))
  · intro a b e
    have := Fin.mk.inj (h5 e)
    have ha := a.2; have hb := b.2
    exact Fin.ext (by omega)
  · intro a b e
    have := Fin.mk.inj (h5 e)
    have ha := a.2; have hb := b.2
    omega

end GlobalTheory.AscFin.FrameBF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsetPlaceVectorsAndSteps
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SubsetVecs

open GlobalTheory.FinPl.PutIn

variable {D : D7} {S T : HSp D} {ι : Type} [DecidableEq ι]

def prodD (a : ι → AE D) (Ψ : ι → WO S T → ℂ) (s : Finset ι) (y : WO S T) : ℂ :=
  if IsHalf (∑ w ∈ s, a w) y then ∏ w ∈ s, Ψ w (a w • y) else 0

theorem sum_mul_zero {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) {s : Finset ι} {w : ι} (hw : w ∉ s) :
    (∑ v ∈ s, a v) * a w = 0 := by
  rw [Finset.sum_mul]
  exact Finset.sum_eq_zero fun v hv => ho v w fun h => hw (h ▸ hv)

theorem prodD_empty (a : ι → AE D) (Ψ : ι → WO S T → ℂ) (Λ : AddSubgroup (WO S T)) :
    prodD a Ψ ∅ = halfInd 0 Λ := by
  funext y
  unfold prodD halfInd
  rw [Finset.sum_empty, Finset.prod_empty]
  by_cases h : IsHalf (0 : AE D) y
  · rw [if_pos h, if_pos ⟨(GlobalTheory.VecProd.isHalf_zero_iff y).1 h ▸ Λ.zero_mem, h⟩]
  · rw [if_neg h, if_neg fun h' => h h'.2]

theorem prodD_insert {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) (Ψ : ι → WO S T → ℂ) {s : Finset ι} {w : ι}
    (hw : w ∉ s) : prodD a Ψ (insert w s) = tens (a w) (prodD a Ψ s) (Ψ w) := by
  funext y
  have h0 := sum_mul_zero ho hw
  have hiff : IsHalf (a w + ∑ v ∈ s, a v) y ↔ IsHalf (∑ v ∈ s, a v) (y - a w • y) :=
    GlobalTheory.VecProd.isHalf_add_iff h0 y
  have hp : ∏ v ∈ s, Ψ v (a v • (y - a w • y)) = ∏ v ∈ s, Ψ v (a v • y) :=
    Finset.prod_congr rfl fun v hv => by
      rw [smul_sub, smul_smul, ho v w fun h => hw (h ▸ hv), zero_smul, sub_zero]
  rw [tens_apply]
  unfold prodD
  rw [Finset.sum_insert hw, Finset.prod_insert hw, hp]
  by_cases h : IsHalf (a w + ∑ v ∈ s, a v) y
  · rw [if_pos h, if_pos (hiff.1 h), mul_comm]
  · rw [if_neg h, if_neg fun h' => h (hiff.2 h'), zero_mul]

theorem prodD_congr (a : ι → AE D) {Ψ Ψ' : ι → WO S T → ℂ} {s : Finset ι} (h : ∀ w ∈ s, Ψ w = Ψ' w) :
    prodD a Ψ s = prodD a Ψ' s := by
  funext y
  unfold prodD
  rw [Finset.prod_congr rfl fun w hw => congrFun (h w hw) _]

theorem prodD_sb {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) (hi : ∀ w, a w * a w = a w)
    {Λ : AddSubgroup (WO S T)} (hΛ : ∀ w, ∀ u ∈ Λ, a w • u ∈ Λ) {Ψ : ι → WO S T → ℂ}
    (hΨ : ∀ w, IsSBHalf (a w) Λ (Ψ w)) (s : Finset ι) : IsSBHalf (∑ w ∈ s, a w) Λ (prodD a Ψ s) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [prodD_empty a Ψ Λ, Finset.sum_empty]
    exact GlobalTheory.isSBHalf_halfInd _ _
  | insert w s hw ih =>
    rw [prodD_insert ho Ψ hw, Finset.sum_insert hw, add_comm]
    exact Factor.isSBHalf_tens (sum_mul_zero ho hw) (hi w) (hΛ w) ih (hΨ w)

theorem prodD_ind {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) (hi : ∀ w, a w * a w = a w)
    {Λ : AddSubgroup (WO S T)} (hΛ : ∀ w, ∀ u ∈ Λ, a w • u ∈ Λ) (s : Finset ι) :
    prodD a (fun w => halfInd (a w) Λ) s = halfInd (∑ w ∈ s, a w) Λ := by
  induction s using Finset.induction_on with
  | empty => rw [prodD_empty a _ Λ, Finset.sum_empty]
  | insert w s hw ih =>
    rw [prodD_insert ho _ hw, Finset.sum_insert hw, add_comm, ih]
    have h := HalfOff.tens_vac (sum_mul_zero ho hw) (hi w) Λ (hΛ w)
    rwa [one_smul, one_smul] at h

theorem exists_chain [Fintype ι] {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0)
    (hi : ∀ w, a w * a w = a w) (hinf : ∀ w, infPart D (a w) = 0) {Ψ : ι → WO S T → ℂ}
    (hΨ : ∀ w, IsSBHalf (a w) (latO S T ΛS ΛT fun _ => True) (Ψ w)) {f₀ f : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) (∑ w, a w) (latO S T ΛS ΛT fun _ => True) 1 f₀
      (prodD a Ψ Finset.univ) f) :
    ∃ V : Finset ι → WO S T → ℂ, V ∅ = f₀ ∧ V Finset.univ = f ∧ (∀ s, IsThetaFunO ψ S T (V s)) ∧
      ∀ s w, w ∉ s → IsThetaAt ψ (symplO S T) (heisO ψ S T) (a w) (latO S T ΛS ΛT fun _ => True) 1 (V s) (Ψ w)
        (V (insert w s)) := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
  have hΛ : ∀ w, ∀ u ∈ (latO S T ΛS ΛT fun _ => True), a w • u ∈ (latO S T ΛS ΛT fun _ => True) :=
    fun w u hu => GlobalTheory.CosetRow.smul_mem_latO_idem _ _ (hi w) hu
  let mix : Finset ι → ι → WO S T → ℂ := fun s w =>
    if w ∈ s then Ψ w else halfInd (a w) (latO S T ΛS ΛT fun _ => True)
  have hmix : ∀ s w, IsSBHalf (a w) (latO S T ΛS ΛT fun _ => True) (mix s w) := fun s w => by
    by_cases h : w ∈ s
    · simp only [mix, if_pos h]; exact hΨ w
    · simp only [mix, if_neg h]; exact GlobalTheory.isSBHalf_halfInd _ _
  have hV0 : Tm (prodD a (mix ∅) Finset.univ) = f₀ := by
    rw [prodD_congr a (Ψ' := fun w => halfInd (a w) (latO S T ΛS ΛT fun _ => True))
      (fun w _ => if_neg (Finset.notMem_empty w)), prodD_ind ho hi hΛ]
    have h := hTm.vac
    rwa [one_smul] at h
  have hstep : ∀ s w, w ∉ s → IsThetaAt ψ (symplO S T) (heisO ψ S T) (a w) (latO S T ΛS ΛT fun _ => True) 1
      (Tm (prodD a (mix s) Finset.univ)) (Ψ w) (Tm (prodD a (mix (insert w s)) Finset.univ)) := by
    intro s w hw
    have hne : w ∉ Finset.univ.erase w := Finset.notMem_erase w _
    have hu : (Finset.univ : Finset ι) = insert w (Finset.univ.erase w) :=
      (Finset.insert_erase (Finset.mem_univ w)).symm
    have e1 : prodD a (mix s) Finset.univ = tens (a w) (prodD a (mix s) (Finset.univ.erase w))
        (halfInd (a w) (latO S T ΛS ΛT fun _ => True)) := by
      conv_lhs => rw [hu]
      rw [prodD_insert ho _ hne]
      simp only [mix, if_neg hw]
    have e2 : prodD a (mix (insert w s)) Finset.univ = tens (a w) (prodD a (mix s) (Finset.univ.erase w)) (Ψ w) := by
      conv_lhs => rw [hu]
      rw [prodD_insert ho _ hne, prodD_congr a (Ψ := mix (insert w s)) (Ψ' := mix s) fun v hv => by
        have hvw : v ≠ w := Finset.ne_of_mem_erase hv
        simp only [mix, Finset.mem_insert, hvw, false_or]]
      simp only [mix, if_pos (Finset.mem_insert_self w s)]
    have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) ((∑ v ∈ Finset.univ.erase w, a v) + a w)
        (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm := by
      rwa [Finset.sum_erase_add _ _ (Finset.mem_univ w)]
    have hM := Factor.isPlaceModel_tensR D ψ S T _ (a w) _ _ _ f₀ Tm (sum_mul_zero ho hne) (hi w) (hΛ w)
      (fun _ _ => Iff.rfl) (prodD_sb ho hi hΛ (hmix s) (Finset.univ.erase w)) hTm'
    rw [e1, e2]
    exact ⟨⟨_, hM⟩, fun T' hT' => GlobalTheory.PlaceVec.placeModel_unique hψ hS hT (hi w) (hinf w) hM hT' (hΨ w)⟩
  refine ⟨fun s => Tm (prodD a (mix s) Finset.univ), hV0, ?_, fun s => ?_, hstep⟩
  · rw [hall Tm hTm]
    exact congrArg Tm (prodD_congr a fun w hw => if_pos hw)
  · induction s using Finset.induction_on with
    | empty => beta_reduce; rw [hV0]; exact h₀
    | insert w s hw ih => exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (hstep s w hw) ih

theorem idemAt_of_single {a : AE D} {w : Pl D.host.E} (h : IsIdemSum a {w}) : Formalism.L2.NTheta.IsIdemAt a w := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  rw [Finset.sum_singleton]
  exact hes w (Finset.mem_singleton_self w)

theorem sum_eq {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {a : P → AE D}
    (ha : ∀ w, IsIdemSum (a w) {w.1}) : ∑ w, a w = e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [← Finset.sum_coe_sort P es]
  exact Finset.sum_congr rfl fun w _ => by
    rw [GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt (idemAt_of_single (ha w)), GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt (hes w.1 w.2)]

theorem orth {a b : AE D} {v w : Pl D.host.E} (ha : IsIdemSum a {v}) (hb : IsIdemSum b {w}) (h : v ≠ w) : a * b = 0 := by
  have h1 := cpt_of_isIdemAt (idemAt_of_single ha)
  have h2 := cpt_of_isIdemAt (idemAt_of_single hb)
  refine ae_ext ?_ fun Q => ?_
  · rw [map_mul, GlobalTheory.PlaceVec.idemSum_infPart ha, zero_mul, map_zero]
  · rw [map_mul, map_mul, map_zero, map_zero]
    by_cases hQ : Q = v
    · rw [h2.2 Q (hQ ▸ h), mul_zero]
    · rw [h1.2 Q hQ, zero_mul]

theorem map_cpt_smul {a : AE D} {w : Pl D.host.E} (ha : IsIdemSum a {w}) {m n : ℕ} (y : Mx D m n) :
    ((a • y).map fun x => cpt w (toEAf D x)) = y.map fun x => cpt w (toEAf D x) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [map_mul, map_mul, (cpt_of_isIdemAt (idemAt_of_single ha)).1, one_mul]

theorem subset_vectors : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∃ V : Finset (locPl ch.G t) → SchDown ch.G t, V ∅ = (fun j : Fin D.R.m => ch.rm.vT D.R.m j) ∧ V Finset.univ = fd ∧ (∀ S j, IsThetaFunO ch.W.ψ _ _ (V S j)) ∧ ∀ (S : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∉ S → ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) (eL w) (V S j) (fun y => if IsHalf (eL w) y then φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (V (insert w S) j) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t e he φ hφ fd hfd eL heL
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hAA : ∀ w ∈ locPl ch.G t, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
    intro w hw
    have hb := GlobalTheory.FunObj.Good.badInt_notMem hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hch.guard t) hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_nat hN
  have ho : ∀ v w, v ≠ w → eL v * eL w = 0 := fun v w h => orth (heL v) (heL w) fun h' => h (Subtype.ext h')
  have hi : ∀ w, eL w * eL w = eL w := fun w => GlobalTheory.PlaceVec.idemSum_mul_self (heL w)
  have hinf : ∀ w, infPart D (eL w) = 0 := fun w => GlobalTheory.PlaceVec.idemSum_infPart (heL w)
  have hsum := sum_eq he heL
  have key : ∀ j : Fin D.R.m, ∃ V : Finset (locPl ch.G t) → Sch ch.G (.down t D.R.m j), V ∅ = ch.rm.vT D.R.m j ∧
      V Finset.univ = fd j ∧ (∀ S, IsThetaFunO ch.W.ψ _ _ (V S)) ∧
      ∀ (S : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∉ S → IsLocVec ch.W (.mu t D.R.m j) (eL w) (V S) (fun y => if IsHalf (eL w) y then φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (V (insert w S)) := by
    intro j
    have hS : IsSelfDualC (ch.G.pS (.mu t D.R.m j)) (ch.G.latS (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m j) ⟨le_rfl, j.2.le⟩).sd
    have hT : IsSelfDualC (ch.G.pT (.mu t D.R.m j)) (ch.G.latT (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m ((j : ℕ) + 1)) ⟨le_rfl, j.2⟩).sd
    have hβS := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ)) le_rfl j.2.le
    have hβT := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ) + 1) le_rfl j.2
    have hmem : GlobalTheory.SplitFlip.Edge.theta D.R.m j ∈ GlobalTheory.SplitFlip.oppositePath D.R.m := by
      simp [GlobalTheory.SplitFlip.oppositePath]
    let Ψ : locPl ch.G t → WO (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j)) → ℂ := fun w y =>
      if IsHalf (eL w) y then φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0
    have hΨ : ∀ w, IsSBHalf (eL w) (latO (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j))
        (ch.G.latS (.mu t D.R.m j) : Set _) (ch.G.latT (.mu t D.R.m j) : Set _) fun _ => True) (Ψ w) := by
      intro w
      have hin : ∀ v : ({w.1} : Finset (Pl D.host.E)), v.1 ∈ locPl ch.G t := fun v => by
        rw [Finset.mem_singleton.1 v.2]; exact w.2
      have hSB := GlobalTheory.VecsLast.isSBHalf_frames hS hT hβS hβT (heL w) (fun v hv => hAA v (hin ⟨v, hv⟩))
        (fun v => GlobalTheory.VecsLast.coordHom ch.S.B t v.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩)
        (fun v z => GlobalTheory.VecsLast.coordHom_int_iff ch.S.B t v.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ z)
        (fun v => depthAt ch.G v.1) (fun v => φ ⟨v.1, hin v⟩ (.theta D.R.m j))
        (fun v => (GlobalTheory.VecsLast.natDatum_props (hφ ⟨v.1, hin v⟩ _ hmem)).1)
        (fun v => (GlobalTheory.VecsLast.natDatum_props (hφ ⟨v.1, hin v⟩ _ hmem)).2)
      haveI : Subsingleton ({w.1} : Finset (Pl D.host.E)) :=
        ⟨fun a b => Subtype.ext ((Finset.mem_singleton.1 a.2).trans (Finset.mem_singleton.1 b.2).symm)⟩
      convert hSB using 1
      funext y
      rw [Fintype.prod_subsingleton _ ⟨w.1, Finset.mem_singleton_self _⟩]
      rfl
    have hprod : prodD eL Ψ Finset.univ = fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0 := by
      funext y
      unfold prodD
      rw [hsum]
      refine if_congr Iff.rfl (Finset.prod_congr rfl fun w _ => ?_) rfl
      refine (if_pos (Factor.half_of_idem (hi w) y)).trans ?_
      exact congrArg (fun z => φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ z)) (map_cpt_smul (heL w) y)
    obtain ⟨V, h1, h2, h3, h4⟩ := exists_chain ch.W.ψ_std ch.W.θ_is hS hT ho hi hinf hΨ
      (ch.rm.vT_is t D.R.m j le_rfl j.2).2.theta (f := fd j) (by rw [hsum, hprod]; exact (hfd j).2)
    exact ⟨V, h1, h2, h3, fun S w hw => ⟨hΨ w, h4 S w hw⟩⟩
  choose V h1 h2 h3 h4 using key
  exact ⟨fun S j => V j S, funext h1, funext h2, fun S j => h3 j S, fun S w hw j => h4 j S w hw⟩

end GlobalTheory.SubsetVecs

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingJointDataJointlySmoothThetaEvenIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaJoint

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {M : Vol G} {t : T}


set_option maxHeartbeats 1000000 in
theorem isBiTheta_lastDat (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j 0 hj))
    (g : GA D (G.V (.grid D.R.m j)))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ)
    (hΦ₁ : IsThetaFunO W.ψ _ _ Φ₁) (hΦ₂ : IsThetaFunO W.ψ _ _ Φ₂) :
    IsBiTheta W.ψ _ _ _ (lastDat W hM j hj vN g Φ₁ Φ₂) := by
  have hΨ : IsThetaFunO W.ψ _ _ ((lastAt G W t hM j hj vN).s.om (g, 1) Φ₁) := (lastAt G W t hM j hj vN).s.weil.om_pres _ _ hΦ₁
  have hΞ : IsThetaFunO W.ψ (besAt G hM j 0 hj vN).V₀ (G.V (.top (j + 1)))
      (GlobalTheory.Unf.flatBF (lastAt G W t hM j hj vN).s ((lastAt G W t hM j hj vN).s.om (g, 1) Φ₁)) :=
    (GlobalTheory.LastRed.val_zero (lastAt G W t hM j hj vN).s hΨ).1
  have hΦ₂' : IsThetaFunO W.ψ (G.V (.top (j + 1))) (G.V (.grid D.R.m D.R.m))
      (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w)) := GlobalTheory.RankZeroVac.isThetaFunction_comp_wittExtendByZero _ _ hΦ₂
  exact GlobalTheory.LastBiTheta.isBiTheta_lastBi D W.ψ W.ψ_std (besAt G hM j 0 hj vN).V₀ (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)
    (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) (G.V (.grid D.R.m D.R.m)) (pLine D) (besAt G hM j 0 hj vN).o
    (topOrthAt G (show D.R.m = j + 1 + 1 by omega)) lastTau LastSeeSawStep.lastTau_gram _ _ hΞ hΦ₂'


set_option maxHeartbeats 1000000 in
theorem isBiTheta_contr (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j (σ + 1) hj))
    (vN' : GlobalTheory.Unf.VolN (besDecAt G (j + 1 + 1) σ (by omega))) (vL : GlobalTheory.Unf.VolM D _ _)
    (Ψ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Ψ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m (j + 1 + 1))) → ℂ)
    (h₁ : IsThetaFunO W.ψ _ _ Ψ₁) (h₂ : IsThetaFunO W.ψ _ _ Ψ₂) :
    IsBiTheta W.ψ (G.V (.top j)) (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1)))
      (GlobalTheory.Unf.contr (linkAt hM j σ hj vN (by omega) vN') (G.V (.top (j + 1))) vL
      (GlobalTheory.Unf.flatBF (B := besAt G hM j _ hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega))
        (stepAt G W t hM j (by omega) (besDecAt G j _ hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))) Ψ₁)
      (GlobalTheory.Unf.flatFB (J := jacAt G hM (j + 1) (σ + 1) (by omega)) (B := besAt G hM (j + 1 + 1) σ (by omega) vN')
        (stepAt G W t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
          (besDecAt G (j + 1 + 1) σ (by omega))) Ψ₂)) := by
  let B := besAt G hM j (σ + 1) hj vN
  let J := jacAt G hM (j + 1) (σ + 1) (by omega)
  let B' := besAt G hM (j + 1 + 1) σ (by omega) vN'
  let s₁ : GlobalTheory.Unf.StepBF W.ψ B J :=
    stepAt G W t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
  let s₂ : GlobalTheory.Unf.StepFB W.ψ J B' :=
    stepAt G W t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
  have t₁ : IsThetaFunO W.ψ B.V₀ J.W₀ (GlobalTheory.Unf.flatBF s₁ Ψ₁) :=
    (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (_root_.GlobalTheory.Unf.Flat.flatLaw D) W.ψ).1 _ B J s₁ _ h₁
  have t₂ : IsThetaFunO W.ψ J.W₀ B'.V₀ (GlobalTheory.Unf.flatFB s₂ Ψ₂) :=
    (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (_root_.GlobalTheory.Unf.Flat.flatLaw D) W.ψ).2 _ J B' s₂ _ h₂
  exact (GlobalTheory.ContrComb.contr_comb_main D W.ψ W.ψ_std _ _ B B' (linkAt hM j σ hj vN (by omega) vN') _ vL _ _ t₁ t₂).1

theorem castSch_theta' {k n : ℕ} (e : n = D.R.m) (f : WO (G.V (.grid D.R.m k)) (G.V (.grid D.R.m n)) → ℂ)
    (hf : IsThetaFunO W.ψ _ _ f) : IsThetaFunO W.ψ _ _ (castSch G e f) := by
  subst e
  exact hf

theorem dite_pred {α : Type} (P : α → Prop) {c : Prop} [Decidable c] {a : c → α} {b : ¬c → α} (ha : ∀ h, P (a h))
    (hb : ∀ h, P (b h)) : P (dite c a b) := by
  by_cases h : c
  · rw [dite_eq_left h]; exact ha h
  · rw [dite_eq_right h]; exact hb h


set_option maxHeartbeats 1000000 in
theorem isBiTheta_conAt (hM : M.Is t) (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j)) (h : Pts G) (j : ℕ) :
    IsBiTheta W.ψ _ _ _ (conAt W hM Φ h j) := by
  unfold conAt
  refine dite_pred (IsBiTheta W.ψ _ _ _) (fun h0 => ?_) (fun _ => dite_pred (IsBiTheta W.ψ _ _ _) (fun hj => ?_) (fun _ => ?_))
  · exact isBiTheta_lastDat W hM j h0 _ _ _ _ (hΦ ⟨j, by omega⟩) (castSch_theta' W _ _ (hΦ ⟨j + 1, by omega⟩))
  · refine isBiTheta_contr W hM j _ hj _ _ _ _ _ ?_ ?_
    · exact (W.om_is (.mu t D.R.m j) ⟨le_rfl, by omega⟩).om_pres _ _ (hΦ ⟨j, by omega⟩)
    · exact (W.om_is (.mu t D.R.m (j + 1)) ⟨le_rfl, by omega⟩).om_pres _ _ (hΦ ⟨j + 1, by omega⟩)
  · exact GlobalTheory.TriStep.isBiTheta_zero'

theorem main : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t Φ τ, IsFlipFin t ch.S.B ch.rm Φ τ → ∀ (M : Vol ch.G) (hM : M.Is t), ∀ d ∈ τ.support, ∀ P h,
    ∀ j, Even j → j < D.R.m → IsBiTheta ch.W.ψ _ _ _ (conAt ch.W hM (fockD ch.W t d.2 P) h j) := by
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ t Φ τ hτ M hM d hd P h j _ _
  obtain ⟨e, he, φ, hφ, -⟩ := hτ
  exact isBiTheta_conAt ch.W hM _ (fun a => GlobalTheory.DownFock.isThetaFunO_fock_down ch.rm t D.R.m a le_rfl a.2 he ((hφ d hd).2 a) (P a)) h j

end GlobalTheory.ThetaJoint
end
end

