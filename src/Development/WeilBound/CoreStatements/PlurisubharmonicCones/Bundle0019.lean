module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.TendstoEpsT
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.TendstoArFun
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0028
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0151
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0020
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0118
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginComparisonSubset
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0029
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0014
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.RootIdxLast
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.HtLabelCongr
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.JoinNormal
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0016
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0244
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0048
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.PullCst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp SheetDecomposition

noncomputable section

namespace LevelTowerAlt.Comparison₂

theorem pull_cst' {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)]
    [∀ k, Fintype (J' k)] {κ : K → K'} {v : (Σ k, J k) → Σ k, J' k} (hv : IsBlockMap κ v) :
    IsPullHerm κ v (PF.cst J) (PF.cst J') := by
  refine ⟨?_, fun z => rfl⟩
  show (0 : K' → ℤ) = pullDeg κ 0
  funext k
  by_cases hk : ∃ a, κ a = k
  · obtain ⟨a, rfl⟩ := hk
    exact (hv.1.extend_apply (0 : K → ℤ) (0 : K' → ℤ) a).symm
  · exact (Function.extend_apply' (0 : K → ℤ) (0 : K' → ℤ) _ hk).symm

theorem root_eq {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N n : ℕ} {M : Top.RootModel Ψ N}
    {S : PB.AnSys (Top.dimFl Ψ N) (Option (Ψ × Fin N))} (R : Top.RealTie M S n) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ S.t₀)
    (c : Option (Ψ × Fin N) → ℤ) :
    (Top.combLine (fun o : Option (Ψ × Fin N) => o.elim (PF.cst M.ι) (M.x t)) c).a =
      (Top.combLine (fun o : Option (Ψ × Fin N) => o.elim (PF.cst M.ι) fun r => R.Re.line (some r) t)
        fun o => o.elim (c none) (gapc (c ∘ some))).a ∧ ∀ z ∈ mcPts M.P,
    (Top.combLine (fun o : Option (Ψ × Fin N) => o.elim (PF.cst M.ι) (M.x t)) c).h z =
      (Top.combLine (fun o : Option (Ψ × Fin N) => o.elim (PF.cst M.ι) fun r => R.Re.line (some r) t)
        fun o => o.elim (c none) (gapc (c ∘ some))).h z := by
  refine ⟨?_, fun z hz => ?_⟩
  · simp only [Top.combLine, Fintype.sum_option, Option.elim, R.Re.line_deg, M.x_deg]
    congr 1
    refine (sum_gapc (c ∘ some) M.xdeg).symm.trans (Finset.sum_congr rfl fun r _ => ?_)
    rw [R.fund_deg]
  · refine Real.log_injOn_pos (HermLine.pos _ _ hz.1) (HermLine.pos _ _ hz.1) ?_
    rw [log_comb _ _ hz.1, log_comb _ _ hz.1]
    simp only [Fintype.sum_option, Option.elim, ← zsmul_eq_mul]
    congr 1
    refine (sum_gapc (c ∘ some) fun r => Real.log ((M.x t r).h z)).symm.trans (Finset.sum_congr rfl fun r _ => ?_)
    rw [R.fund_reg r.1 r.2 t h0 h1 z hz]

set_option maxHeartbeats 1000000 in
theorem tie_of (hC : Common) (hR : Replace) (hB : BaseSide) : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → ∃ (K₃ : Type) (_ : Fintype K₃) (ι₃ : K₃ → Type) (_ : ∀ k, Fintype (ι₃ k)) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ι₃ k) (P₃ : Ideal (MRing ι₃)) (e r : ℕ) (cf : Fin r → ℝ) (Mt : ℝ → HermLine ι₃) (Nt : ℝ → Fin r → Fin e → HermLine ι₃) (δ : ℝ), IsBlockMap κ v ∧ IsArithVar P₃ (Dc.n + 1 + e) ∧ imageZ v P₃ = mCoordIdeal Dc.y ∧ 0 < δ ∧ (∀ t m i, (Nt t m i).a = (Nt 1 m i).a) ∧ (∀ t m i, IsSmoothHerm (Nt t m i)) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IsPullHerm κ v (muReg X.H X.S B t) (Mt t)) ∧ Tendsto (fun t => ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m))) (𝓝[>] 0) (𝓝 (δ * T.PPc II B a (Top.testPoly T.j))) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * ptsIntegral (e := Dc.n + e) P₃ (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t) (Nt 1 m) i).h z)) (fun _ => 1) = δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) := by
  intro hAg _ _ hG _ E _ _ _ _ H D Xo l c Y _ T o II _ hEx hII hp hq B B₁ a K _ J _ Ω _ _ W _ _ Dc O Lt _ _ _ X Or _ hBB hqp
    hbg hsm hGood hgen hS
  have hI : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hK : ResK.ResKStatement := hG.2.2.2.2.1
  have hSeq : o.S B = T.bad ∪ Dc.SB B := by
    ext r
    rw [o.S_iff, Top.RootTower.InS, Finset.mem_union, ComponentData.SB, Finset.mem_filter, hS]
    have := (o.bad_iff r).1
    by_cases h : r ∈ T.bad
    · simp [h, (this h).1]
    · simp only [h, or_false, false_or, not_false_eq_true, and_true]
      exact ⟨fun h => ⟨⟨h.1, h.2.trans hBB⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  obtain ⟨K₃, _, ρ, _, κ₁, v₁, κ₂, v₂, Ω₃, _, _, y, β, b, hb₁, hb₂, he₁, he₂, har, hβ, hβn, hrk, hbd, hiso⟩ :=
    hC hG E H D Xo l c Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) II K J Ω W Dc X.H T.bad Or B hSeq
      (fun p hp hd => (o.bad_iff p).2 ⟨hp, (hd.mul_left 2).mul_right _⟩) (o.omVB B a) (hEx.2 B a) hp hbg hsm hGood hgen
  have hmono := OrLinked.mono_int' c
  obtain ⟨x₀, hx₀⟩ := _root_.GlobalTheory.CompanionTheory.Ar.GenOpen.gen_open E H D l _ c _ _ Y _ _ _ _ _ (o.Or B a).𝔐 hmono
  have alg := _root_.GlobalTheory.CompanionTheory.Ar.RootAlg.algOver_of_immersion E H D l _ c _ _ Y _ _ _ _ (o.Or B a) (spMap (o.Or B a).𝔐.fn ≫ x₀) (by
    rw [Category.assoc, ← hx₀]; exact (o.Or B a).𝔐.fn_over) hmono (hEx.1 a)
  have : Nonempty (RootIx D) := ⟨(Classical.choice (_root_.GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H).2.1, ⟨0, by omega⟩)⟩
  obtain ⟨K', _, ρ', _, κ, v, y', hb, hy, hfield, har', hcore⟩ := anCore hR hB hI hK hII ((o.Or B a).Re.comap some) alg
    (gapc (muExp D.p)) (Top.combLine (o.Or B a).sing (muExp D.p)) (by
      simp only [Top.combLine, (o.Or B a).sing_deg]
      refine (sum_gapc _ _).symm.trans (Finset.sum_congr rfl fun r _ => ?_)
      rw [← (o.Or B a).fund_deg]
      rfl) (fun x hx => by
      refine (log_comb _ _ ((o.Or B a).Re.R.mem x x ((o.Or B a).Re.R.mem_U x)).1).trans ?_
      simp only [← zsmul_eq_mul]
      refine (sum_gapc _ fun r => Real.log (((o.Or B a).sing r).h _)).symm.trans (Finset.sum_congr rfl fun r _ => ?_)
      exact congrArg _ ((o.Or B a).fund_sing r.1 r.2 x hx).symm) X.H X.S B X.S_tied hb₁ hb₂ he₁ he₂ har hβ hβn hbd hiso
  have hjb := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.join_block_maps
  have hc₁ := (hjb.2.2 _ _ K₃ ρ K' ρ' κ₁ v₁ κ v hb₁ hb).1
  have hc₂ := (hjb.2.2 K J K₃ ρ K' ρ' κ₂ v₂ κ v hb₂ hb).1
  have hy₁ : y' ∘ v ∘ v₁ = y ∘ v₁ := by rw [← hy]; rfl
  have e₁ : imageZ (v ∘ v₁) (mCoordIdeal y') = (T.M B a).P := by rw [hjb.2.1 _ _ K' ρ' _ _ Ω₃ y' hc₁, hy₁, he₁]
  have e₂ : imageZ (v ∘ v₂) (mCoordIdeal y') = mCoordIdeal Dc.y := by
    rw [hjb.2.1 K J K' ρ' _ _ Ω₃ y' hc₂, ← he₂, ← hy]
    rfl
  have hp₁ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.hermLine_pull_blockMap _ _ K' ρ' _ _ hc₁
  have hp₂ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.hermLine_pull_blockMap K J K' ρ' _ _ hc₂
  choose pl hpl using fun A => (hp₁.1 A).exists
  choose Mt hMt using fun t => (hp₂.1 (muReg X.H X.S B t)).exists
  have hcore' := hcore Mt (fun t r => pl ((o.Or B a).Re.line (some r) t)) hMt fun t r => hpl _
  let RT := (Top.realOf o.toTowerOrigin).tie B a
  have ht₀ : 0 < (o.Sys a).t₀ := ((o.Sys a).reg none).1
  let x' : ℝ → Option (RootIx D) → HermLine (T.M B a).ι := fun t o' => o'.elim (PF.cst _) ((T.M B a).x t)
  have hx' : ∀ t cc, IsSmoothHerm (Top.combLine (x' t) cc) := fun t cc => (_root_.GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj _ _ _ _ cc).1 fun o' => by
    cases o'
    exacts [PF.cst_smooth, (T.M B a).x_smooth _ _]
  have hreg := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log K J II _ Ω W Dc X.H X.M X.S B X.S_tied
  set e := IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) with he
  have key : ∀ (a' b' : ℕ) (cc : Fin b' → Option (RootIx D) → ℤ), a' + b' = Top.dimFl (CMType H) (D.p + D.q) + 1 →
      Tendsto (fun t => II K' ρ' (mCoordIdeal y') (a' + b') (Fin.append (fun _ : Fin a' => Mt t)
          fun j => pl (Top.combLine (x' t) (cc j))) - e * II _ _ (T.M B a).P (a' + b') (Fin.append
            (fun _ : Fin a' => Top.combLine ((T.M B a).x t) (muExp D.p)) fun j => Top.combLine (x' t) (cc j))) (𝓝[>] 0) (𝓝 0) := by
    intro a' b' cc hab
    refine (hcore' a' b' (fun j o' => o'.elim (cc j none) (gapc (cc j ∘ some))) hab).congr' ?_
    filter_upwards [hreg, Ioc_mem_nhdsGT ht₀] with t h1 h2
    have hA : IsArithVar (mCoordIdeal y') (a' + b') := hab ▸ har'
    have hls : ∀ cc, IsSmoothHerm (Top.combLine (fun o' : Option (RootIx D) => o'.elim (PF.cst ρ')
        fun r => pl ((o.Or B a).Re.line (some r) t)) cc) := fun cc => (_root_.GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj _ _ _ _ cc).1 fun o' => by
      cases o'
      exacts [PF.cst_smooth, hp₁.2.1 _ _ (hpl _) ((o.Or B a).Re.line_smooth _ t h2.1 h2.2)]
    have hq : ∀ cc : Option (RootIx D) → ℤ, (Top.combLine (fun o' : Option (RootIx D) => o'.elim (PF.cst ρ')
        fun r => pl ((o.Or B a).Re.line (some r) t)) fun o' => o'.elim (cc none) (gapc (cc ∘ some))).a =
          (pl (Top.combLine (x' t) cc)).a ∧ ∀ z ∈ mcPts (mCoordIdeal y'),
        (Top.combLine (fun o' : Option (RootIx D) => o'.elim (PF.cst ρ')
        fun r => pl ((o.Or B a).Re.line (some r) t)) fun o' => o'.elim (cc none) (gapc (cc ∘ some))).h z =
          (pl (Top.combLine (x' t) cc)).h z := by
      intro cc
      have h3 := (_root_.GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines.isoLineOn_comb_trans_symm_pull K' ρ' _ ∅ har'.2.1 (Set.empty_subset _)).2.2.2 _ _ _ _ _
        (fun o' : Option (RootIx D) => o'.elim (PF.cst _) fun r => (o.Or B a).Re.line (some r) t)
        (fun o' : Option (RootIx D) => o'.elim (PF.cst ρ') fun r => pl ((o.Or B a).Re.line (some r) t))
        (fun o' => o'.elim (cc none) (gapc (cc ∘ some))) hc₁ fun o' => by
          cases o'
          exacts [pull_cst' hc₁, hpl _]
      have h4 := root_eq RT h2.1 h2.2 cc
      exact ⟨h3.1.trans ((congrArg _ h4.1.symm).trans (hpl _).1.symm),
        fun z hz => (h3.2 z).trans ((h4.2 _ (e₁ ▸ hp₁.2.2.1 _ _ hz)).symm.trans ((hpl _).2 z).symm)⟩
    have hm := hq fun o' => o'.elim 0 (muExp D.p)
    rw [comb_some] at hm
    have hMs := hp₂.2.1 _ _ (hMt t) h1.1
    have hxs := (_root_.GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj _ _ _ _ (muExp D.p)).1 ((T.M B a).x_smooth t)
    congr 1
    · refine hI.metricLocal K' ρ' _ (hII.1 K' ρ') _ _ _ _ hA ?_ ?_ ?_ ?_ <;> refine Fin.addCases (fun j => ?_) fun j => ?_ <;>
        simp only [Fin.append_left, Fin.append_right]
      exacts [hMs, hls _, hMs, hp₁.2.1 _ _ (hpl _) (hx' _ _), (hq _).1, fun _ _ => trivial, (hq _).2]
    · have h5 := hII.2.2.1 _ _ K' ρ' _ _ Ω₃ y' (a' + b') (Fin.append
          (fun _ : Fin a' => Top.combLine ((T.M B a).x t) (muExp D.p)) fun j => Top.combLine (x' t) (cc j))
        (Fin.append (fun _ : Fin a' => pl (Top.combLine ((T.M B a).x t) (muExp D.p))) fun j => pl (Top.combLine (x' t) (cc j)))
        hc₁ hA (by rw [e₁, hab]; exact (T.M B a).arith)
        (Fin.addCases (fun j => by simpa using hxs) fun j => by simpa using hx' _ _)
        (Fin.addCases (fun j => by simpa using hpl _) fun j => by simpa using hpl _)
      rw [e₁, hy₁, hfield] at h5
      rw [← h5]
      refine hI.metricLocal K' ρ' _ (hII.1 K' ρ') _ _ _ _ hA ?_ ?_ ?_ ?_ <;> refine Fin.addCases (fun j => ?_) fun j => ?_ <;>
        simp only [Fin.append_left, Fin.append_right]
      exacts [hls _, hls _, hp₁.2.1 _ _ (hpl _) hxs, hp₁.2.1 _ _ (hpl _) (hx' _ _), hm.1, (hq _).1, hm.2, (hq _).2]
  let ee := (Fintype.equivFin (PairIx (CMType H) D.p D.q)).symm
  have hdim : Dc.n + Fintype.card (PairIx (CMType H) D.p D.q) = Top.dimFl (CMType H) (D.p + D.q) := by
    rw [Or.n_eq, count_pairs]
  let cF := fun i (o' : Option (RootIx D)) => o'.elim 0 (fibCoef (ee i))
  have hδ : (0 : ℝ) < e * (T.M B a).δ := mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hrk)) (Nat.cast_pos.2 (T.M B a).δ_pos)
  have happ : ∀ (t : ℝ) (n : ℕ), (Fin.append (fun _ : Fin n => Top.combLine ((T.M B a).x t) (muExp D.p))
      fun j => Top.combLine (x' t) (cF j)) = fun j => Top.combLine ((T.M B a).x t)
        (Fin.append (fun _ : Fin n => muCoef (CMType H) D.p D.q) (fun j => fibCoef (ee j)) j) := by
    intro t n
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp only [Fin.append_left, Fin.append_right]
    · rfl
    · exact comb_some _ _ _
  have hNa : ∀ t i, (pl (Top.combLine (x' t) (cF i))).a = (pl (Top.combLine (x' 1) (cF i))).a := fun t i => by
    rw [(hpl _).1, (hpl _).1, comb_some, comb_some]
    simp only [Top.combLine, (T.M B a).x_deg]
  have hNs : ∀ t i, IsSmoothHerm (pl (Top.combLine (x' t) (cF i))) := fun t i => hp₁.2.1 _ _ (hpl _) (hx' _ _)
  refine ⟨K', inferInstance, ρ', inferInstance, κ ∘ κ₂, v ∘ v₂, mCoordIdeal y', _, 1, fun _ => 1, Mt,
    fun t _ i => pl (Top.combLine (x' t) (cF i)), e * (T.M B a).δ, hc₂, by rw [Nat.add_right_comm, hdim]; exact har', e₂, hδ,
    fun t _ i => hNa t i, fun t _ i => hNs t i, Eventually.of_forall hMt, ?_, ?_⟩
  · have h1 := key (Dc.n + 1) _ cF (by rw [Nat.add_right_comm, hdim])
    have h2 := (tendsto_arFun (T.M B a) ((_root_.GlobalTheory.CompanionTheory.Ar.Top.real_tower_convergence_I2 hAg hI II hII _ _ T (Top.realOf o.toTowerOrigin)).1 B a)
      (Top.toA (Top.testPoly T.j))).const_mul (e * (T.M B a).δ : ℝ)
    have h3 := h1.add h2
    rw [zero_add] at h3
    refine h3.congr fun t => ?_
    rw [happ, ← arFun_prod (T.M B a) hII t (by rw [Nat.add_right_comm, hdim]), ← test_factor' ee hqp Or.n_eq, o.j_eq]
    simp only [Finset.univ_unique, Finset.sum_singleton, _root_.one_mul]
    ring
  · have h1 := key Dc.n _ (Fin.snoc (α := fun _ => Option (RootIx D) → ℤ) cF fun o' => o'.elim 1 0) (by rw [← hdim]; rfl)
    have hA : IsArithVar (mCoordIdeal y') (Dc.n + Fintype.card (PairIx (CMType H) D.p D.q) + 1) := hdim ▸ har'
    have hs : ∀ t t', IsSmoothHerm (muReg X.H X.S B t) → ∀ j, IsSmoothHerm (Fin.append (fun _ : Fin Dc.n => Mt t)
        (fun i => pl (Top.combLine (x' t') (cF i))) j) := fun t t' ht =>
      Fin.addCases (fun j => by simpa using hp₂.2.1 _ _ (hMt t) ht) fun j => by simpa using hNs _ _
    have hcst : ∀ t t' u u', IsSmoothHerm (muReg X.H X.S B t) → IsSmoothHerm (muReg X.H X.S B u) →
        ptsIntegral (mCoordIdeal y') (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t)
          (fun i => pl (Top.combLine (x' t') (cF i))) i).h z)) (fun _ => 1) =
        ptsIntegral (mCoordIdeal y') (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt u)
          (fun i => pl (Top.combLine (x' u') (cF i))) i).h z)) (fun _ => 1) := fun t t' u u' ht hu =>
      pts_deg hI hA (hs t t' ht) (hs u u' hu) (Fin.addCases (fun j => by
        simp only [Fin.append_left, (hMt _).1, muReg, smoothRep_a]
        rfl) fun j => by simp only [Fin.append_right, hNa])
    filter_upwards [hreg] with u hu
    simp only [Finset.univ_unique, Finset.sum_singleton, _root_.one_mul]
    refine sub_eq_zero.1 (neg_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds (h1.congr' ?_)))
    filter_upwards [hreg] with t ht
    have a1 : (fun j => pl (Top.combLine (x' t) (Fin.snoc (α := fun _ => Option (RootIx D) → ℤ) cF (fun o' => o'.elim 1 0) j))) =
        Fin.snoc (α := fun _ => HermLine ρ') (fun j => pl (Top.combLine (x' t) (cF j))) (PF.cst ρ') := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [comb_none]
      exact (hp₁.1 _).unique (hpl _) (pull_cst' hc₁)
    have a2 : (fun j => Top.combLine (x' t) (Fin.snoc (α := fun _ => Option (RootIx D) → ℤ) cF (fun o' => o'.elim 1 0) j)) =
        Fin.snoc (α := fun _ => HermLine (T.M B a).ι) (fun j => Top.combLine (x' t) (cF j)) (PF.cst _) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
      exact comb_none _ _
    rw [a1, a2, Fin.append_snoc, Fin.append_snoc, happ]
    have a3 := LevelTowerAlt.ii_cst_int hII.1 hA _ (hs t t ht.1)
    have a4 := LevelTowerAlt.ii_cst_int hII.1 (show IsArithVar (T.M B a).P _ from hdim ▸ (T.M B a).arith)
      (fun j => Top.combLine ((T.M B a).x t)
        (Fin.append (fun _ : Fin Dc.n => muCoef (CMType H) D.p D.q) (fun j => fibCoef (ee j)) j))
      fun j => (_root_.GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj _ _ _ _ _).1 ((T.M B a).x_smooth t)
    rw [← geoFun_pts (T.M B a) hI t hdim, ← test_factor ee hqp Or.n_eq] at a4
    rw [hcst t t u 1 ht.1 hu.1] at a3
    refine (congrArg₂ (fun r s : ℝ => r - e * s) a3 a4).trans ?_
    rw [o.j_eq]
    ring

end LevelTowerAlt.Comparison₂
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.PullDegSum
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace LevelTowerAlt.Comparison₂

section Last

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) [Fintype (CMType H)]

theorem prod_last {M : Type} [CommMonoid M] (F : CMType H × Fin (D.p + D.q) → M) :
    ∏ r, (if D.p ≤ (r.2 : ℕ) then F r else 1) = ∏ a, F (lastRoot D a) := by
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Fin.prod_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  rw [Finset.prod_eq_one (fun i _ => if_neg (by omega)), one_mul]
  simp only [le_add_iff_nonneg_right, zero_le, if_true]
  exact (Fintype.prod_equiv Fin.revPerm (fun a => F (lastRoot D (τ, a))) (fun j => F (τ, Fin.natAdd D.p j))
    (fun a => rfl)).symm

theorem sum_last {M : Type} [AddCommMonoid M] (F : CMType H × Fin (D.p + D.q) → M) :
    ∑ r, (if D.p ≤ (r.2 : ℕ) then F r else 0) = ∑ a, F (lastRoot D a) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  rw [Finset.sum_eq_zero (fun i _ => if_neg (by omega)), zero_add]
  simp only [le_add_iff_nonneg_right, zero_le, if_true]
  exact (Fintype.sum_equiv Fin.revPerm (fun a => F (lastRoot D (τ, a))) (fun j => F (τ, Fin.natAdd D.p j))
    (fun a => rfl)).symm

end Last

theorem pullDeg_sum {K K' I : Type} [Fintype I] {κ : K → K'} (hκ : Function.Injective κ) (a : I → K → ℤ) :
    pullDeg κ (∑ j, a j) = ∑ j, pullDeg κ (a j) := by
  funext x
  simp only [pullDeg, Finset.sum_apply]
  by_cases hx : ∃ y, κ y = x
  · obtain ⟨y, rfl⟩ := hx
    simp only [hκ.extend_apply, Finset.sum_apply]
  · simp only [Function.extend_apply' _ _ _ hx, Pi.zero_apply, Finset.sum_const_zero]

set_option maxHeartbeats 1000000 in
theorem common (h₁ : LevelFree) (h₂ : MuHodge) : Common := by
  intro hG E _ _ _ _ H D Xo l c Y S RM Sys Fx oR II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B hS hdisc hvR hR4 hp hbg hsm hgood hgen
  classical
  subst hS
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := OrLinked.mono_int' c
  have czR : CharZero RM.Ω := charZero_of_injective_ringHom oR.𝔐.cst.injective
  obtain ⟨a1, a2, a3, a4⟩ := _root_.LevelTowerAlt.component_data_height_identity E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B
  have hfree : ∀ p ∈ S₀ ∪ Dc.SB B, HT.HTFree Or.𝔐 p := fun p hp' => by
    rcases Finset.mem_union.1 hp' with h | h
    · exact hgood.1 p h
    · exact hgood.2 p (Finset.mem_filter.1 h).1
  have hlev : ∀ p ∈ S₀ ∪ Dc.SB B, ∀ q, InFibre Or.𝔐.ξ p q →
      Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ 4) q = Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) q := fun p hp' =>
    h₁ hG.2.2.2.2.2.2.1 E H D l (Xo l) c Y _ Ω K J Dc.y (Or.𝔐.withS _ a1 a2 a3 a4) p hp' (by omega) (hfree p hp')
  let B₄ := levFour Or.𝔐 _ a1 a2 a3 a4 hlev
  have hB₄ : ∀ s, B₄.V s = Or.𝔐.VS (S₀ ∪ Dc.SB B) s := patch_four Or.𝔐 _ hlev

  have eg : genPt oR.𝔐.ξ₀ = genPt Or.𝔐.ξ₀ := by
    have g1 := RegAtDom.map_genPt oR.𝔐.fn_over
    have g2 := RegAtDom.map_genPt (show GlobalTheory.CompanionTheory.Ar.Dominates oR.𝔐.ξ Fx.ξf oR.𝔐.f oR.g from oR.g_over)
    rw [hgen, ← g1, g2]
  obtain ⟨ψ, hψ⟩ := FlagPull.exists_iso oR.𝔐.gen₀ Or.𝔐.gen₀ eg
  have hfin : letI := (Or.𝔐.fn.comp ψ.toRingHom).toAlgebra; Module.Finite oR.𝔐.Ω₀ Ω := by
    have f1 : Or.𝔐.fn.Finite := by
      let _ := Or.𝔐.fn.toAlgebra
      exact Module.finite_of_finrank_pos (Or.cover.2 ▸ Or.cover.1)
    exact RingHom.Finite.comp f1 (RingHom.Finite.of_surjective _ ψ.surjective)
  obtain ⟨Ω₃, _, i₁, i₂, hi, hf₁⟩ := OrLinked.exists_tensor_field oR.𝔐.Ω₀ RM.Ω Ω oR.𝔐.fn _ hfin
  have cz : CharZero Ω₃ := charZero_of_injective_ringHom i₁.injective
  have fd₁ : FiniteDimensional i₁.fieldRange Ω₃ := FiniteDimensional.of_finrank_pos (by
    rw [OrLinked.finrank_fieldRange]
    let _ := i₁.toAlgebra
    exact Module.finrank_pos)
  obtain ⟨K₃, _, ρ, _, κ₁, v₁, κ, v, y, Z, ξ, g₁, g₂, bm₁, bm₂, hy₁, hy₂, I1, I2, har, hbir, hall, htie, hnorm, hd₁, hd₂, hrk⟩ :=
    join_normal i₁ i₂ RM.y Dc.y _ oR.𝔐.ξ Or.𝔐.ξ RM.arith RM.birational fd₁ oR.𝔐.all Or.𝔐.all oR.𝔐.tie Or.𝔐.tie
  obtain ⟨x₁, hx₁'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.GenOpen.gen_open E H D l (Xo l) c _ _ Y _ RM.Ω RM.K RM.ι RM.y oR.𝔐 hmono
  obtain ⟨x₂, hx₂'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.GenOpen.gen_open E H D l (Xo l) c _ _ Y _ Ω K J Dc.y Or.𝔐 hmono
  have hx₁ : oR.𝔐.ξ ≫ oR.𝔐.f = (spMap oR.𝔐.fn ≫ x₁) ≫ Y.j := by
    rw [Category.assoc, ← hx₁']; exact oR.𝔐.fn_over
  have hx₂ : Or.𝔐.ξ ≫ Or.𝔐.f = (spMap Or.𝔐.fn ≫ x₂) ≫ Y.j := by
    rw [Category.assoc, ← hx₂']; exact Or.𝔐.fn_over
  have hdisc' : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀ ∪ Dc.SB B := fun p h1 h2 =>
    Finset.mem_union_left _ (hdisc p h1 h2)
  obtain ⟨𝔐, a, j₁, m₁, q1, q2, q3, q4, q5, q6, q7, -, q9⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.HcptPull.hodgeCpt_pull E H D l (Xo l) c _ _ Y _ RM.Ω Ω₃ i₁ RM.K K₃ RM.ι ρ RM.y y oR.𝔐 _ Z ξ g₁ hx₁ hdisc'
      (fun p hp s => (hvR p hp).2 s) hall htie hnorm hd₁
  have hdom₁ : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ oR.𝔐.ξ (a.hom ≫ g₁) i₁ := by
    show 𝔐.ξ ≫ a.hom ≫ g₁ = _
    rw [← Category.assoc, q1]
    exact hd₁
  have hdom₂ : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ Or.𝔐.ξ (a.hom ≫ g₂) i₂ := by
    show 𝔐.ξ ≫ a.hom ≫ g₂ = _
    rw [← Category.assoc, q1]
    exact hd₂
  have hf𝔐 : 𝔐.f = (a.hom ≫ g₁) ≫ oR.𝔐.f := by rw [q2, Category.assoc]
  obtain ⟨Fl, hbF, -, -, hlF⟩ := FlagPull.flag_pull E H D l (Xo l) c _ _ Y _ RM.Ω Ω₃ i₁ RM.K K₃ RM.ι ρ RM.y y oR.𝔐 𝔐
    (a.hom ≫ g₁) j₁ m₁ κ₁ v₁ oR.Fl bm₁ hy₁ hdom₁ hf𝔐 q3 q4 q6 q7 q9 fd₁
  have hZ : g₂ ≫ Or.𝔐.f = g₁ ≫ oR.𝔐.f := by
    refine OrLinked.map_eq_of_generic hnorm hall Y.s Y.proj ?_
    have e1 : ξ ≫ g₁ = spMap i₁ ≫ oR.𝔐.ξ := hd₁
    have e2 : ξ ≫ g₂ = spMap i₂ ≫ Or.𝔐.ξ := hd₂
    have e3 : oR.𝔐.ξ ≫ oR.𝔐.f = spMap oR.𝔐.fn ≫ oR.𝔐.ξ₀ := oR.𝔐.fn_over
    have e4 : Or.𝔐.ξ ≫ Or.𝔐.f = spMap Or.𝔐.fn ≫ Or.𝔐.ξ₀ := Or.𝔐.fn_over
    rw [← Category.assoc, ← Category.assoc, e1, e2, Category.assoc, Category.assoc, e3, e4, ← hψ, ← Category.assoc,
      ← Category.assoc, ← Category.assoc, OrLinked.spMap_spMap', OrLinked.spMap_spMap', OrLinked.spMap_spMap', hi, RingHom.comp_assoc]
  have hvb₄ : ∀ p ∈ S₀ ∪ Dc.SB B, ∀ s, ((Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ 4)).map (Or.𝔐.Vgen s).dualRestrict).IsVBOn
      {q | InFibre Or.𝔐.ξ p q} (labelRk D s) ⊤ := fun p hp' s =>
    vbOn_congr (L := (Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ Or.𝔐.R p)).map (Or.𝔐.Vgen s).dualRestrict) (fun q hq => by
      simp only [Lat.map]
      rw [hlev p hp' q hq]) ((hfree p hp').2 s)
  have hf₄ : (a.hom ≫ g₂) ≫ Or.𝔐.f = 𝔐.f := by rw [q2, Category.assoc, hZ]
  obtain ⟨j, m, hj, hpt, hV⟩ := pull_on (i := i₂) B₄ 𝔐 (a.hom ≫ g₂) _ hx₂ hdisc'
    hvb₄ hdom₂ hf₄ (fun p hp' => by rw [q5]; exact hR4 p hp')
  have hx : 𝔐.ξ ≫ 𝔐.f = (spMap i₁ ≫ spMap oR.𝔐.fn ≫ x₁) ≫ Y.j := by
    have e1 : 𝔐.ξ ≫ a.hom ≫ g₁ = spMap i₁ ≫ oR.𝔐.ξ := hdom₁
    rw [hf𝔐, ← Category.assoc, e1, Category.assoc, hx₁]
    simp only [Category.assoc]
  obtain ⟨β, d, hβ, hβn, hint⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_form_interior E H D l (Xo l) c _ _ Y _ Ω₃ K₃ ρ y 𝔐 _ hx hmono
  have hdown : ∀ (z : Sp ℂ ⟶ 𝔐.X) (w : (Σ k, ρ k) → ℂ), CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
      CoordsAt Or.𝔐.ξ Dc.y (z ≫ a.hom ≫ g₂) (fun p => w (v p)) ∧ Or.𝔐.Interior (z ≫ a.hom ≫ g₂) := fun z w hw hz =>
    ⟨HodgePull.coordsAt_pull hdom₂ 𝔐.tie.gen Or.𝔐.tie.cover bm₂ hy₂ (𝔐.all _) (Or.𝔐.all _) hw,
      (abLocus_pullback abLocusOne Or.𝔐.t.semi m.cart.1 _).2 hz⟩
  refine ⟨K₃, inferInstance, ρ, inferInstance, κ₁, v₁, κ, v, Ω₃, inferInstance, cz, y, β, d, bm₁, bm₂, I1, I2, har, hβ, hβn,
    hrk, fun w hw hb hBd => ?_, fun L L' hL hL' => ?_⟩
  · obtain ⟨z, hz, hI⟩ := hint w hw hb
    obtain ⟨c1, c2⟩ := hdown z w hz hI
    exact (Or.bd _ _ c1).1 hBd c2
  obtain ⟨ch₀, hch₀⟩ := Or.𝔐.tie.cover ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
  obtain ⟨n, f, cc, -, -, hsum, hloc⟩ := Hd.locally ch₀ hch₀.1
  obtain ⟨l₀⟩ : Nonempty (Fin n) := by
    by_contra h
    have := not_nonempty_iff.1 h
    simp at hsum
  obtain ⟨bb, -, lam, -, hΛ⟩ := hloc l₀
  have hs : ∀ τ k, ∃ z, z ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - z ∈ Or.𝔐.Vgen (Or.bg τ) := fun τ k => by
    obtain ⟨a, ha, z, hz, h⟩ := Submodule.mem_sup.1
      (Or.i_range τ ▸ LinearMap.mem_range_self (Or.i τ) (bb τ (tailIdx Dc.j_le_N k)))
    exact ⟨z, hz, by rw [← h, add_sub_cancel_right]; exact ha⟩
  choose s hs using hs
  obtain ⟨hsi, hdeg⟩ := _root_.LevelTowerAlt.det_lattice_tensor_isDegOn_muTwDeg E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B bb s _ hs hΛ
  have hmet := h₂ hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B bb s _ hs hΛ
  have hn : Dc.N - Dc.j = D.q := by
    rcases Or.side with ⟨-, -, h⟩ | ⟨h, -, -⟩
    · rw [h, Or.N_eq]; omega
    · rw [hbg] at h
      obtain ⟨τ⟩ : Nonempty (CMType H) := (_root_.GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H).2.1
      exact absurd (congrFun h τ) (by simp)
  simp only [hsm] at hs hdeg hmet
  choose Lp hLp using fun r => ((_root_.GlobalTheory.CompanionTheory.Ar.Cmp.hermLine_pull_blockMap RM.K RM.ι K₃ ρ κ₁ v₁ bm₁).1 (oR.sing r)).exists
  have hroot : Fl.RootLines (fun r => (Lp r).a) fun r => i₁ (oR.e r) := by
    have h := hlF _ _ oR.lines
    have e : (fun r => (Lp r).a) = fun r => pullDeg κ₁ (RM.xdeg r) := funext fun r => by rw [(hLp r).1, oR.sing_deg]
    rwa [e]
  have hiso := core 𝔐 Fl hbir Lp hroot
    (fun r => HodgePull.hodgeLine_pull E H D l (Xo l) c _ _ Y _ RM.Ω Ω₃ i₁ RM.K K₃ RM.ι ρ RM.y y oR.𝔐 𝔐 (a.hom ≫ g₁) j₁ m₁ κ₁
      v₁ oR.Fl bm₁ hy₁ hdom₁ hf𝔐 q3 q4 q6 q7 q9 Fl hbF r _ _ _ (oR.hodge r) (hLp r))
    Or.𝔐.t Or.𝔐.tie.gen Or.𝔐.tie.cover Or.𝔐.M (fun τ => Or.𝔐.VS (S₀ ∪ Dc.SB B) (.inr τ)) hdom₂ m j hj hpt
    (fun τ => (hV _).trans (by rw [hB₄]; rfl)) (fun τ => Or.𝔐.Vgen (.inr τ)) (fun τ => a4 (.inr τ)) hn s hsi
    (fun τ k => (hs τ k).1) (muVert Hd B) _ hdeg bm₂ hy₂
    (fun z w hw hz => hmet _ _ (hdown z w hw hz).1 (hdown z w hw hz).2) L L' ?_ (fun w => ?_) hL'
  · obtain ⟨f₁, f₂, hf, hdef⟩ := hiso
    exact ⟨f₁, f₂, hf, fun w hw => hdef w (hint w hw.1 hw.2)⟩
  · rw [hL.1, ← sum_last D fun r => (Lp r).a]
    show pullDeg κ₁ (∑ r, muExp D.p r • (oR.sing r).a) = _
    rw [pullDeg_sum bm₁.1]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold muExp
    split_ifs
    · rw [one_smul, (hLp r).1]
    · rw [zero_smul]
      funext k'
      unfold pullDeg
      by_cases h : ∃ k, κ₁ k = k'
      · obtain ⟨k, rfl⟩ := h
        rw [bm₁.1.extend_apply]
        rfl
      · rw [Function.extend_apply' _ _ _ h]
  · rw [hL.2, ← prod_last D fun r => (Lp r).h w]
    show ∏ r, (oR.sing r).h _ ^ muExp D.p r = _
    refine Finset.prod_congr rfl fun r _ => ?_
    unfold muExp
    split_ifs
    · rw [zpow_one, (hLp r).2]
    · rw [zpow_zero]

end LevelTowerAlt.Comparison₂
end
end

