module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumSqGeAndPhiEqZeroDefinite
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0066
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingLowCoeffMemLeadingAddDeepSpan
section
noncomputable section

namespace GlobalTheory.Containment

section Model

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
  MeasureTheory Topology GlobalTheory.Shares ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_valBasis (X : Data E r) (G : Wt X.Ψ r) {δ m : ℕ} (xs : Fin δ → Frame X.Ψ r)
    (t : Fin m → Frame X.Ψ r → ℂ) (ht : ∀ k, X.IsBddSec G (t k))
    (hs : ∀ v : Fin δ → ℂ, ∃ a : Fin m → ℂ, ∀ j, ∑ k, a k * t k (xs j) = v j) :
    ∃ t' : Fin δ → Frame X.Ψ r → ℂ, (∀ k, X.IsBddSec G (t' k)) ∧ IsValBasisM X xs t' := by
  classical
  choose a ha using fun i : Fin δ => hs (Pi.single i 1)
  have hv : ∀ i j, (∑ k, a i k • t k) (xs j) = (Pi.single i (1 : ℂ) : Fin δ → ℂ) j := fun i j => by
    rw [← ha i j, Finset.sum_apply]; rfl
  have hsum : ∀ (c : Fin δ → ℂ) j, ∑ i, c i * (∑ k, a i k • t k) (xs j) = c j := fun c j => by
    simp only [hv]
    simp [Pi.single_apply]
  refine ⟨fun i => ∑ k, a i k • t k, fun i => ?_, fun v => ⟨v, hsum v⟩, fun c hc => ?_⟩
  · exact Finset.sum_induction _ (X.IsBddSec G) (fun _ _ h1 h2 => bdd_add X h1 h2) (bdd_zero X G)
      fun k _ => bdd_smul X _ (ht k)
  · funext j
    rw [← hsum c j, hc j]; rfl

theorem division_one (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (hm : Margins X Xa)
    (hfin : ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L),
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x)
    {m : ℕ} (t : Fin m → Frame X.Ψ r → ℂ) (ht : ∀ k, X.IsBddSec Xa.Fp (t k))
    (hs : ∀ v : Fin Fl.δ → ℂ, ∃ a : Fin m → ℂ, ∀ j, ∑ k, a k * t k (Fl.xs j) = v j)
    (f : Frame X.Ψ r → ℂ) (hf : f ∈ X.SSgt (Xa.Fp + Xa.T • Xa.L) Xa.c1)
    (cc : (Fin (nd X) → ℕ) → Fin m → ℂ)
    (hO : ∀ j, (fun z : V (nd X) => f (cpt X (Fl.xs j) z) -
      leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ (Xa.T - nd X)) :
    ∃ h : (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), h α ∈ X.SS (Xa.Fp + nd X • Xa.L)) ∧
      ∀ x ∈ X.dom, f x - leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc x =
        ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), monoM X Fl.s α x * h α x := by
  obtain ⟨-, hm2, hm3, -, hcusp⟩ := hm
  have hPD := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X
  have hFM := GlobalTheory.DriftCovolume.finMu_unconditional r X
  obtain ⟨x0, ho, FF, hFF, hmu⟩ := id hFM
  obtain ⟨hb, hint⟩ := DivStartStatement_holds r X Xa Fl hPD hFM m t ht x0 ho FF hFF f hf.1
    ((GlobalTheory.highModes_le_pow_w r X Xa f hf).2 x0 FF hFF hmu) cc
  obtain ⟨t', ht', hbas⟩ := exists_valBasis X Xa.Fp Fl.xs t ht hs
  have hl0 : ∀ x, leadM X Fl.s Fl.w0 t' Xa.T (Xa.T - nd X) 0 x = 0 := fun x => by simp [leadM]
  have hvan := GlobalTheory.vanS_of_isBigO r X Xa Fl (Xa.T - nd X) _ hb.1.1.continuousOn hO
  obtain ⟨h, hh, hx⟩ := divCoreStatement_holds r X Xa Fl hPD hFM hm2 hm3 (hcusp _)
    (by simpa using hcusp 0) (hcusp _) hfin _ t' ht' hbas x0 ho FF hFF _ (hcusp _ _ hb) hint 0
    (by simpa only [hl0, sub_zero] using hvan)
  exact ⟨h, fun α hα => hcusp _ _ (hh α hα), fun x hx' => by simpa only [hl0, sub_zero] using hx x hx'⟩

theorem division_one' (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (hm : Margins X Xa) {D Tn : ℕ}
    (hD : nd X = D) (hT : Xa.T = Tn)
    (hfin : ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (Xa.Fp + Tn • Xa.L),
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x)
    {m : ℕ} (t : Fin m → Frame X.Ψ r → ℂ) (ht : ∀ k, X.IsBddSec Xa.Fp (t k))
    (hs : ∀ v : Fin Fl.δ → ℂ, ∃ a : Fin m → ℂ, ∀ j, ∑ k, a k * t k (Fl.xs j) = v j)
    (f : Frame X.Ψ r → ℂ) (hf : f ∈ X.SSgt (Xa.Fp + Tn • Xa.L) Xa.c1)
    (cc : (Fin D → ℕ) → Fin m → ℂ)
    (hO : ∀ j, (fun z : V (nd X) => f (cpt X (Fl.xs j) z) - ∑ α ∈ multiLt D (Tn - D), ∑ k,
      cc α k * (∏ q, Fl.s (Fin.cast hD.symm q) (cpt X (Fl.xs j) z) ^ α q) *
        Fl.w0 (cpt X (Fl.xs j) z) ^ (Tn - ∑ q, α q) * t k (cpt X (Fl.xs j) z))
        =O[𝓝 0] fun z => ‖z‖ ^ (Tn - D)) :
    ∃ h : (Fin D → ℕ) → Frame X.Ψ r → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple D (Tn - D), h α ∈ X.SS (Xa.Fp + D • Xa.L)) ∧
      ∀ x ∈ X.dom, f x - ∑ α ∈ multiLt D (Tn - D), ∑ k,
        cc α k * (∏ q, Fl.s (Fin.cast hD.symm q) x ^ α q) * Fl.w0 x ^ (Tn - ∑ q, α q) * t k x =
        ∑ α ∈ Finset.Nat.antidiagonalTuple D (Tn - D), (∏ q, Fl.s (Fin.cast hD.symm q) x ^ α q) * h α x := by
  subst hD hT
  exact division_one X Xa Fl hm hfin t ht hs f hf cc hO

theorem eventually_diff (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {P : Frame X.Ψ r → ℂ}
    (hP : DifferentiableOn ℂ P X.dom) :
    ∀ᶠ z in 𝓝 (0 : V (nd X)), DifferentiableAt ℂ (fun z => P (cpt X x z)) z := by
  have h0 : (0 : V (nd X)) ∈ OmF X x := by
    show cpt X x 0 ∈ X.dom
    rw [GlobalTheory.LeadJets.cpt_zero]; exact hx
  filter_upwards [(OntoB.isOpen_OmF X x).mem_nhds h0] with z hz
  exact (OntoB.hol_comp X x hP).differentiableAt ((OntoB.isOpen_OmF X x).mem_nhds hz)

theorem division_all {κ : Type} (X : κ → Data E r) (Xa : ∀ k, ArchInM (X k)) (Fl : ∀ k, FlatM (X k) (Xa k))
    (hm : ∀ k, Margins (X k) (Xa k)) {D Tn : ℕ} (hD : ∀ k, nd (X k) = D) (hT : ∀ k, (Xa k).T = Tn)
    (hfin : ∀ k, ∃ (K : ℕ) (g : Fin K → Frame (X k).Ψ r → ℂ), ∀ f ∈ (X k).SS ((Xa k).Fp + Tn • (Xa k).L),
      ∃ c : Fin K → ℂ, ∀ x ∈ (X k).dom, f x = ∑ i, c i * g i x)
    {m : ℕ} (t : Fin m → ∀ k, Frame (X k).Ψ r → ℂ) (ht : ∀ i k, (X k).IsBddSec (Xa k).Fp (t i k))
    (hs : ∀ v : (Σ k, Fin (Fl k).δ) → ℂ, ∃ a : Fin m → ℂ, ∀ p, ∑ i, a i * t i p.1 ((Fl p.1).xs p.2) = v p)
    (f : ∀ k, Frame (X k).Ψ r → ℂ) (hf : ∀ k, f k ∈ (X k).SSgt ((Xa k).Fp + Tn • (Xa k).L) (Xa k).c1) :
    ∃ (cc : (Fin D → ℕ) → Fin m → ℂ) (h : ∀ k, (Fin D → ℕ) → Frame (X k).Ψ r → ℂ),
      (∀ k, ∀ α ∈ Finset.Nat.antidiagonalTuple D (Tn - D), h k α ∈ (X k).SS ((Xa k).Fp + D • (Xa k).L)) ∧
      ∀ k, ∀ x ∈ (X k).dom, f k x - ∑ α ∈ multiLt D (Tn - D), ∑ i,
        cc α i * (∏ q, (Fl k).s (Fin.cast (hD k).symm q) x ^ α q) * (Fl k).w0 x ^ (Tn - ∑ q, α q) * t i k x =
        ∑ α ∈ Finset.Nat.antidiagonalTuple D (Tn - D),
          (∏ q, (Fl k).s (Fin.cast (hD k).symm q) x ^ α q) * h k α x := by
  classical
  have hs0 : ∀ k j a, (Fl k).s a ((Fl k).xs j) = 0 := fun k j =>
    ((Fl k).S_eq _ ((Fl k).xs_mem j)).2 ⟨j, 1, one_mem _, nmat (X k) 0, GlobalTheory.LeadJets.nmat_zero_mem_Bor _, by
      rw [GlobalTheory.LeadJets.rmul_nmat_zero, GlobalTheory.LeadJets.lact_one]⟩
  obtain ⟨cc, hcc⟩ := GlobalTheory.JetsPure.main (Σ k, Fin (Fl k).δ) (Fin m) D Tn (Tn - D) (by omega)
    (fun p => nd (X p.1)) (fun p => finCongr (hD p.1))
    (fun p z => f p.1 (cpt (X p.1) ((Fl p.1).xs p.2) z))
    (fun p z => (Fl p.1).w0 (cpt (X p.1) ((Fl p.1).xs p.2) z))
    (fun p q z => (Fl p.1).s (Fin.cast (hD p.1).symm q) (cpt (X p.1) ((Fl p.1).xs p.2) z))
    (fun p i z => t i p.1 (cpt (X p.1) ((Fl p.1).xs p.2) z))
    (fun p => by
      have hx := (Fl p.1).xs_mem p.2
      refine (eventually_diff _ hx (hf p.1).1.1.1.1).and ((eventually_diff _ hx (Fl p.1).weightForm_vanishes.1.1.1.1).and
        (Filter.Eventually.and ?_ ?_))
      · exact Filter.eventually_all.2 fun q => eventually_diff _ hx ((Fl p.1).s_van _).1.1.1.1
      · exact Filter.eventually_all.2 fun i => eventually_diff _ hx (ht i p.1).1.1)
    (fun p => ⟨by simpa only [GlobalTheory.LeadJets.cpt_zero] using (Fl p.1).w0_ne p.2,
      fun q => by simpa only [GlobalTheory.LeadJets.cpt_zero] using hs0 p.1 p.2 _, (Fl p.1).coord p.2⟩)
    (by simpa only [GlobalTheory.LeadJets.cpt_zero] using hs)
  have hsk : ∀ k, ∀ v : Fin (Fl k).δ → ℂ, ∃ a : Fin m → ℂ, ∀ j, ∑ i, a i * t i k ((Fl k).xs j) = v j := by
    intro k v
    obtain ⟨a, ha⟩ := hs fun p => if hp : p.1 = k then v (Fin.cast (by rw [hp]) p.2) else 0
    exact ⟨a, fun j => by simpa using ha ⟨k, j⟩⟩
  choose h hh hx using fun k => division_one' (X k) (Xa k) (Fl k) (hm k) (hD k) (hT k) (hfin k)
    (fun i => t i k) (fun i => ht i k) (hsk k) (f k) (hf k) cc fun j => hcc ⟨k, j⟩
  exact ⟨cc, h, hh, hx⟩

end Model

section Record

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem sp_le_span_fin {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} (R : Rdg X)
    (u : WeightFamilies.Wt D j) : ∃ (m : ℕ) (g : Fin m → R.Y → ℂ), R.sp u Set.univ ≤ Submodule.span ℂ (Set.range g) := by
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := B.KO) (M := B.Cusp j u)
  refine ⟨m, fun i => R.ev (X.inc u (b i)), Submodule.span_le.2 ?_⟩
  rintro _ ⟨F, -, rfl⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B.KO).1 (hb ▸ Submodule.mem_top : F ∈ Submodule.span B.KO (Set.range b))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, R.ev_smul, SetLike.mem_coe]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem main : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ (CR c : ℝ), c1 = WeightFamilies.c1 D CR Tn c j → (∀ F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tn c j (addL wF wL Tn), ∀ k : (T.U j T.σ₀).Comp, rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j (addL wF wL Tn) k) c1) → ∀ (m : ℕ) (θ : Fin m → R.Y → ℂ), (∀ i, θ i ∈ R.sp wF Set.univ) → Submodule.span ℂ (Set.range (vals xs θ)) = ⊤ → R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn)) ≤ Submodule.span ℂ (Set.range (R.lead w t Tn (a0 D j Tn) θ)) ⊔ R.deep w t ((recPlusN h j hj n).wF0 wL wF) (a0 D j Tn) := by
  classical
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hxs hOnto CR c _ hMg m θ hθ hspan
  have hsp := span_readings_components D T h j hj n R e hR
  have hwt : ∀ (k : (T.U j T.σ₀).Comp) (a : ℕ), laR T j (addL wF wL a) k = (A.Xa k).Fp + a • (A.Xa k).L := fun k a => by
    rw [A.hF, A.hL]
    exact (WtDic.weights_dictionary D T h j hj k).2.2.1 wF wL a
  choose θf hθf hθe using fun i => (hsp wF).1 (θ i) (hθ i)
  have hs : ∀ (i : Fin (WeightFamilies.dimY D j + 1)) (y : R.Y),
      R.s w t i y = ∑ k, t (i, k) * rdR h j (w k) (e y).1 (e y).2.1 := fun i y => by
    unfold Rdg.s
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul, hR.2]
  have hs0 : ∀ y, R.s w t 0 y = (Fl.Fl (e y).1).w0 (e y).2.1 := fun y => by rw [hs, Fl.h0]
  have hs1 : ∀ (q : Fin (WeightFamilies.dimY D j)) y,
      R.s w t q.succ y = (Fl.Fl (e y).1).s (Fin.cast (A.dim _).symm q) (e y).2.1 := fun q y => by
    rw [hs, Fl.hs]; rfl
  have hfin : ∀ k : (T.U j T.σ₀).Comp, ∃ (K : ℕ) (g : Fin K → Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ),
      ∀ f ∈ ((T.U j T.σ₀).X k).SS ((A.Xa k).Fp + Tn • (A.Xa k).L),
        ∃ c : Fin K → ℂ, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f x = ∑ i, c i * g i x := by
    intro k
    obtain ⟨K, g, hg⟩ := sp_le_span_fin R (addL wF wL Tn)
    refine ⟨K, fun i x => if hx : x ∈ ((T.U j T.σ₀).X k).dom then g i (e.symm ⟨k, x, hx⟩) else 0, fun f hf => ?_⟩
    have hmem := (hsp (addL wF wL Tn)).2.1 _ _ (hOnto Tn) (Pi.single k f) fun k' => by
      by_cases hk : k' = k
      · subst hk
        rw [Pi.single_eq_same, hwt]; exact hf
      · rw [Pi.single_eq_of_ne hk, hwt]
        exact (A.mar k').2.2.2.2 _ _ (BoundedSectionAlgebra.bdd_zero _ _)
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hg hmem)
    refine ⟨cf, fun x hx => ?_⟩
    have h1 := congrFun hcf (e.symm ⟨k, x, hx⟩)
    rw [Equiv.apply_symm_apply, Finset.sum_apply] at h1
    simp only [dif_pos hx]
    simpa using h1.symm
  have hsurj : ∀ v : (Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ) → ℂ, ∃ a : Fin m → ℂ, ∀ p,
      ∑ i, a i * θf i p.1 ((Fl.Fl p.1).xs p.2) = v p := by
    intro v
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1
      (hspan ▸ Submodule.mem_top : (fun q => v (en q)) ∈ Submodule.span ℂ (Set.range (vals xs θ)))
    refine ⟨a, fun p => ?_⟩
    obtain ⟨q, rfl⟩ := en.surjective p
    rw [← congrFun ha q, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = a i * θ i (xs q)
    rw [hθe, hxs]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨F, hF, rfl⟩
  obtain ⟨cc, g, hg, hx⟩ := division_all (T.U j T.σ₀).X A.Xa Fl.Fl A.mar A.dim A.hT hfin θf
    (fun i k => by rw [A.hF]; exact (hθf i k).1.1) hsurj (rdR h j F)
    (fun k => by rw [← hwt, A.hc]; exact hMg F hF k)
  have hdec : R.ev ((recPlusN h j hj n).inc (addL wF wL Tn) F) =
      ∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (WeightFamilies.dimY D j) (Tn - WeightFamilies.dimY D j), ∑ i,
        cc α i • (R.mon w t α * R.s w t 0 ^ (Tn - ∑ q, α q) * θ i) +
      ∑ α ∈ Finset.Nat.antidiagonalTuple (WeightFamilies.dimY D j) (Tn - WeightFamilies.dimY D j),
        R.mon w t α * fun y => g (e y).1 α (e y).2.1 := by
    funext y
    rw [hR.2, sub_eq_iff_eq_add'.1 (hx (e y).1 (e y).2.1 (e y).2.2)]
    simp only [Rdg.mon, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Finset.prod_apply,
      Pi.pow_apply, smul_eq_mul, hs0, hs1, hθe, mul_assoc]
  show R.ev ((recPlusN h j hj n).inc (addL wF wL Tn) F) ∈ _
  rw [hdec]
  refine Submodule.add_mem_sup (Submodule.sum_mem _ fun α hα => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(⟨α, GlobalTheory.LeadJets.mem_multiLt.1 hα⟩, i), rfl⟩))
    (Submodule.sum_mem _ fun α hα => Submodule.subset_span
      ⟨α, _, Finset.Nat.mem_antidiagonalTuple.1 hα, ?_, rfl⟩)
  exact (hsp (addL wF wL (WeightFamilies.dimY D j))).2.1 _ _ (hOnto _) (fun k => g k α) fun k => by
    rw [hwt]; exact hg k α hα

end Record

end GlobalTheory.Containment
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumSqGeAndPhiEqZeroDefiniteStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.la1sq_ge_two_f_div_rd_of_p0_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : FD.Data E r), 0 < r → X.p0 = 0 → (∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * FD.herm X.Gm u v) = k) → ∀ x ∈ X.dom, 2 * (I2.PT.f E : ℝ) / I2.PT.rd E ≤ X.firstMinimumSq x ∧ ∀ (q : ℕ) (R0 : ℝ), 1 ≤ I2.PT.rd E → 0 < q → 1 ≤ I2.b0 (E := E) q R0 → I2.phiFD X (I2.th (E := E) q R0) x = 0 := by
  first | exact @GlobalTheory.DefiniteMin.firstMinimumSq_ge_and_phi_eq_zero_definite | exact GlobalTheory.DefiniteMin.firstMinimumSq_ge_and_phi_eq_zero_definite | (intros; apply GlobalTheory.DefiniteMin.firstMinimumSq_ge_and_phi_eq_zero_definite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogTwoMulCountLeMulSize
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem log_two_mul_count_le_mul_size : ∀ (D : D7) (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j) (N : ℕ) (Prw : ℝ), 2 ≤ large₂.sc.L → 0 < w.n → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → OPO large₂ B → 38 * large₂.sc.L + PO D large₂ ≤ Prw → N ≤ 2 * ((D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ B.KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n))) → Real.log N ≤ Prw * (w.size - 1) := by
  intro D B large₂ j w N Prw hL hn hrows hO hPrw hN
  obtain ⟨hg, -, -, -, -, -, -, hX, -⟩ := hrows

  set m : ℕ := D.R.f * D.R.r * w.n with hm
  have hN' : N ≤ (D.host.g 0 * D.host.g 1) ^ m * ((2 * Module.finrank ℚ B.KO) * (1 + WeightAlgebra.DF w) ^ m) := by
    calc N ≤ _ := hN
      _ = _ := by ring
  have hL0 : (0 : ℝ) ≤ large₂.sc.L := by linarith
  have hPO : 0 ≤ PO D large₂ := by unfold PO; positivity
  have hd : Real.log ((2 * Module.finrank ℚ B.KO : ℕ) : ℝ) ≤ PO D large₂ + 1 := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℚ B.KO) with h0 | hpos
    · simp [h0]; linarith
    · have hk : ((Module.finrank ℚ B.KO : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      push_cast
      rw [Real.log_mul (by norm_num) hk]
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9; linarith
      linarith [hO.1]
  have hX' : Real.log ((1 + WeightAlgebra.DF w : ℕ) : ℝ) ≤ 2 * large₂.sc.L := by
    push_cast; exact hX
  have key := log_le_of_le_pow_mul_pow (a := 9 * large₂.sc.L + 1) (c := 2 * large₂.sc.L) (P := PO D large₂ + 1)
    (by linarith) (by linarith) (by linarith) (hg 0) (hg 1) hd hX' hN'

  have hf : 0 < D.R.f := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    have h3 : D.R.f = 2 * D.R.ord := rfl
    omega
  have hr : 0 < D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    have h3 : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hms : (m : ℝ) ≤ w.size - 1 := frn_le_size_sub_one w
  have hPrw0 : 0 ≤ Prw := by linarith
  calc Real.log N ≤ (m : ℝ) * (2 * (9 * large₂.sc.L + 1) + 2 * large₂.sc.L) + (PO D large₂ + 1) := key
    _ ≤ (m : ℝ) * (38 * large₂.sc.L + PO D large₂) := by nlinarith
    _ ≤ (m : ℝ) * Prw := by gcongr
    _ ≤ Prw * (w.size - 1) := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hms hPrw0

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NonemptyHeightOneSpectrumRingOfIntegers
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem nonempty_heightOneSpectrum_ringOfIntegers (K : Type) [Field K] [NumberField K] :
    Nonempty (HeightOneSpectrum (𝓞 K)) := by

  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩⟩

theorem shareRhoP_of_anFacts : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (N : ℕ) (w : Fin N → B.Cusp j wL) (R : Rdg X) (t : Idx D j N → ℂ) (T : ℕ) (CR c : ℝ) (δ : ℕ) (xs : Fin δ → R.Y), AnFacts R w t ka wF T (WeightFamilies.MggK B CR T c j ka) xs → 2 ≤ WeightFamilies.dimY D j → 11 * WeightFamilies.dimY D j ^ 2 ≤ T → LatAt B j ka → ShareRhoP (D := D) (j := j) T (WeightFamilies.rhoP B CR T c j ka) (X.rk ka (B.Mlat j ka)) := by
  intro D B P j X ka wL wF N w R t T CR c δ xs hA hD hT hL
  obtain ⟨la⟩ := nonempty_heightOneSpectrum_ringOfIntegers B.KO

  have hdim : ∀ M : Submodule B.KO (B.Cusp j ka),
      Module.finrank ℂ (R.sp ka M) = Module.finrank B.KO M := fun M =>
    ((_root_.GlobalTheory.Shares.polyDictionary D B P j X R la N wL w t).2.2.2.2.2.2.2 ka M).2
  have hspan : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤ :=
    Submodule.IsFullLattice.span_eq_top (self := hL)

  have hd : X.rk ka (B.Mlat j ka) = Module.finrank B.KO (B.Cusp j ka) := by
    unfold PJ.rk
    rw [hspan, finrank_top]
  have hup : Module.finrank ℂ (R.sp ka Set.univ) = Module.finrank B.KO (B.Cusp j ka) := by
    have h := hdim ⊤
    rwa [Submodule.top_coe, finrank_top] at h

  have hsum := Submodule.finrank_quotient_add_finrank (WeightFamilies.MggK B CR T c j ka)
  have hq := rhoP_eq_finrank B CR T c j ka hspan
  have hlo := hA.lower
  rw [hdim] at hlo
  have key := (_root_.GlobalTheory.card_exponents_and_choose_ratio_bounds (WeightFamilies.dimY D j) T).2 δ (X.rk ka (B.Mlat j ka)) (WeightFamilies.rhoP B CR T c j ka) hD hT
    (by rw [hd, ← hup]; exact hA.upper)
  exact key.2 (by rw [hq, hd, ← hsum]; omega)

end GlobalTheory.Shares
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ScaledFamily
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.ScaledGenerators

theorem span_scaled {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (wL : WeightFamilies.Wt D j)
    (s : 𝓞 B.KO) {N : ℕ} (w0 : Fin N → B.Cusp j wL)
    (h : Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll wL) :
    Submodule.span (𝓞 B.KO) (Set.range fun k => (s : B.KO) • w0 k) = X.WWc s wL := by

  have hfun : (fun k => (s : B.KO) • w0 k) =
      (s • (LinearMap.id : B.Cusp j wL →ₗ[𝓞 B.KO] B.Cusp j wL)) ∘ w0 := by
    funext k
    simp only [Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    first
      | rfl
      | exact algebraMap_smul B.KO s (w0 k)
      | simp
  rw [hfun, Set.range_comp, ← Submodule.map_span, h]
  rfl

theorem scaled_family : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (S : Scal B) (N : ℕ) (w0 : Fin N → B.Cusp j wL) (a b G Prw : ℝ), 0 ≤ a → 0 ≤ b → (∀ σ : B.KO →+* ℂ, Real.log ‖σ (S.sW : B.KO)‖ ≤ a) → Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll wL → (∀ k σ, Real.log (B.supN j wL σ (w0 k)) ≤ b) → a + b ≤ G * wL.size → (∃ Sh : Finset (B.Cusp j wL), Submodule.span (𝓞 B.KO) (Sh : Set (B.Cusp j wL)) = X.WWc S.sW wL ∧ ∃ mx : (B.KO →+* ℂ) → ℝ, (∀ σ, ∀ g ∈ Sh, Real.log (B.supN j wL σ g) ≤ mx σ) ∧ (∑ σ, mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size) ∧ (X.WWc S.sW wL ≤ B.Mlat j wL → Real.log N ≤ Prw * (wL.size - 1) → ∃ Gd : EtaleWeightGaps.GlobalFamilyData X ka wL wF, Gd.TiedW S G Prw) := by
  classical
  intro D B P j X ka wL wF S N w0 a b G Prw ha hb hS hspan hsup hG

  set w : Fin N → B.Cusp j wL := fun k => (S.sW : B.KO) • w0 k with hw
  have hspanw : Submodule.span (𝓞 B.KO) (Set.range w) = X.WWc S.sW wL := span_scaled X wL S.sW w0 hspan

  have hbound : ∀ σ k, Real.log (B.supN j wL σ (w k)) ≤ a + b := by
    intro σ k
    have hmul : B.supN j wL σ (w k) = ‖σ (S.sW : B.KO)‖ * B.supN j wL σ (w0 k) := B.supN_smul j wL σ _ (w0 k)
    rw [hmul]
    by_cases hx : ‖σ (S.sW : B.KO)‖ = 0
    · rw [hx, zero_mul, Real.log_zero]
      linarith
    by_cases hy : B.supN j wL σ (w0 k) = 0
    · rw [hy, mul_zero, Real.log_zero]
      linarith
    rw [Real.log_mul hx hy]
    linarith [hS σ, hsup k σ]

  have hmean : (∑ _σ : B.KO →+* ℂ, (a + b)) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos (Fintype.card (B.KO →+* ℂ)) with h0 | h0
    · rw [h0, Nat.cast_zero, zero_mul, zero_div]
      linarith
    · have hc : (Fintype.card (B.KO →+* ℂ) : ℝ) ≠ 0 := by positivity
      rw [mul_div_cancel_left₀ _ hc]
      exact hG
  refine ⟨⟨Finset.univ.image w, ?_, fun _ => a + b, ?_, hmean⟩, ?_⟩
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hspanw
  · intro σ g hg
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hg
    exact hbound σ k
  · intro hM hN

    refine ⟨{
        N := N
        w := w
        del := 0
        th' := fun i => Fin.elim0 i
        rz := 0
        alz := fun i => Fin.elim0 i
        th0 := fun i => Fin.elim0 i
        zc := fun i => Fin.elim0 i
        rq := 0
        th := fun i => Fin.elim0 i
        iet := 0
        et := 0
        mx := fun _ => a + b }, ?_⟩
    refine ⟨hspanw, ?_, hN, fun σ k => hbound σ k, hmean⟩
    intro k
    apply hM
    rw [← hspanw]
    exact Submodule.subset_span (Set.mem_range_self k)

end GlobalTheory.ScaledGenerators
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRunParametersAtTypePrimesProductStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRunParameters_at_typePrimes_product : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (S : Scal B) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → EtaleWeightGaps.PageSupp D large₂ B C2 A2 nW S wL → RunOK D.host.E D.R.r (WeightAlgebra.DF wL) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL))) D.R.m ∧ 8100 * Real.pi * wL.n * (D.R.m : ℝ) ^ 4 * (I2.dstar (E := D.host.E) D.R.m : ℝ) ^ 4 * I2.RR (E := D.host.E) / (D.host.g 0 * D.host.g 1 : ℕ) ≤ cc D large₂ C2 A2 CR wL ∧ p14 D.host.E D.R.r wL.n D.R.m ≤ (D.R.f * D.R.r * nW * Real.log ((D.host.g 0 : ℝ) * D.host.g 1) + nW * (Real.log 24 + D.R.f * D.R.m * Real.log (4 * D.R.f * D.R.m)) + (D.R.r + 2) * Real.log 2) / 2 ∧ D.R.f * D.R.r * (D.R.r + 1) ≤ 2 * wL.n := by
  first | exact @GlobalTheory.RunParametersAtRecord.run_at_record | exact GlobalTheory.RunParametersAtRecord.run_at_record | (intros; apply GlobalTheory.RunParametersAtRecord.run_at_record <;> assumption)
end

