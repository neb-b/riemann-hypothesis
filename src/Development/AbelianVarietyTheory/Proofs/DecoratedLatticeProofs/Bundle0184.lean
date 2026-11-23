module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Bundle0004
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingClassOffOpenOrbitFixedByUnipotentRadical
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.Dich

theorem offOpen : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ¬ (∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V) → ∃ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C ∧ (∀ n ∈ NI V C, ∃ p : siegel V, γ * io V (n, 1) = p * γ ∧ aP V p = 1) ∧ ∀ δ ∈ GQ V, γ * io V (δ, 1) * γ⁻¹ ∈ siegel V → ∀ n ∈ NI V C, δ * n * δ⁻¹ ∈ NI V C := by
  intro D V γ hγ hopen
  obtain ⟨g, hg, -, hγi⟩ := exists_rat (dblSp V) hγ
  have hgi : g⁻¹ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (dblSp V).gram := inv_mem hg
  set γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E := (g⁻¹).1 with hγidef
  have hU : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γi * dblGram finSumFinEquiv V.gram * γi =
      dblGram finSumFinEquiv V.gram := by
    have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γi * (dblSp V).gram * γi = (dblSp V).gram := hgi
    rwa [gram_hdbl] at h
  set Qd := diagSnd γi with hQd
  set P := leviMat finSumFinEquiv γi with hP
  have hinj : ∀ x, P *ᵥ x = 0 → Qd *ᵥ x = 0 → x = 0 := by
    intro x h1 h2
    have h3 : γi *ᵥ pairVec finSumFinEquiv x x = 0 := by
      rw [mulVec_pairVec_diag, ← hP, ← hQd, h1, h2]
      funext j; simp [pairVec, Sum.elim_zero_zero]
    have h4 : (g.1 * γi) *ᵥ pairVec finSumFinEquiv x x = 0 := by rw [← mulVec_mulVec, h3, mulVec_zero]
    rw [hγidef, Units.mul_inv, one_mulVec] at h4
    funext i
    have := congrFun h4 (finSumFinEquiv (.inl i))
    rwa [pairVec_inl] at this
  by_cases hk : ∀ x, Qd *ᵥ x = 0 → x = 0
  · exact absurd (_root_.GlobalTheory.Core.Rk.Dich.exists_mem_siegel_of_diagSnd D V γ hγ γi hγi hk) hopen
  push Not at hk
  obtain ⟨x0, hx0, hx0ne⟩ := hk
  let W := LinearMap.ker Qd.mulVecLin
  let b := Module.finBasis D.host.E W
  let K : Matrix (Fin V.rank) (Fin (Module.finrank D.host.E W)) D.host.E :=
    Matrix.of fun i j => (b j : Fin V.rank → D.host.E) i
  have hKv : ∀ y, K *ᵥ y = ((∑ j, y j • b j : W) : Fin V.rank → D.host.E) := by
    intro y; funext i
    simp [K, Matrix.mulVec, dotProduct, Submodule.coe_sum, Finset.sum_apply, mul_comm]
  have hbQ : ∀ j, Qd *ᵥ (b j : Fin V.rank → D.host.E) = 0 := fun j => (b j).2
  have hQK : Qd * K = 0 := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hbQ j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, K, Matrix.of_apply, Matrix.zero_apply]
    exact this
  have hspan : ∀ x, Qd *ᵥ x = 0 → ∃ y, x = K *ᵥ y := by
    intro x hx
    refine ⟨b.repr ⟨x, hx⟩, ?_⟩
    rw [hKv, b.sum_repr]
  have hiso : IsIsoFrame V (P * K) := by
    refine ⟨?_, ?_, ?_⟩
    · exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x0, hx0⟩, fun h => hx0ne (congrArg Subtype.val h)⟩
    · refine (Matrix.mulVec_injective_iff (M := P * K)).1 ?_
      intro c c' hc
      rw [← sub_eq_zero] at hc ⊢
      rw [← mulVec_sub, ← mulVec_mulVec] at hc
      have h1 : K *ᵥ (c - c') = 0 := hinj _ hc (by rw [mulVec_mulVec, hQK, zero_mulVec])
      rw [hKv] at h1
      have h2 : (∑ j, (c - c') j • b j : W) = 0 := Subtype.ext h1
      funext j
      exact Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 j
    · have hI := isotropic_diag hU
      rw [← hP, ← hQd] at hI
      rw [Formalism.UG.cT_mul]
      calc Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) K * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P *
            V.gram * (P * K)
          = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) K *
            (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * V.gram * P) * K := by
            simp only [Matrix.mul_assoc]
        _ = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Qd * K) * V.gram * (Qd * K) := by
            rw [hI, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hQK]; simp [Formalism.UG.cT]
  refine ⟨_, P * K, hiso, _root_.GlobalTheory.Core.Rk.Dich.conj_io_unip_siegel D V γ hγ γi hγi _ K hQK hiso, ?_⟩
  intro δ hδ hs n hn
  obtain ⟨d, -, hδm, -⟩ := exists_rat V hδ
  obtain ⟨G, hG, hGe⟩ := _root_.GlobalTheory.Core.Rk.Dich.isoFrame_keep D V γ hγ γi hγi _ K hQK hspan hiso δ hδ d.1 hδm hs
  exact _root_.GlobalTheory.FrameNorm.norm D V _ (P * K) δ hδ d.1 hδm G hG hGe n hn

end GlobalTheory.Core.Rk.Dich

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingVectorFockPairIsCompactFinite
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem delta_isKFinVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → ∀ omh : WRep (dblSp A) B, IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → IsKFinVec omh (Khat A a) (delta A B Φ₁ Φ₂) := by
  intro D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ₁ Φ₂ h₁ h₂
  obtain ⟨-, -, -, hθ, -, -, hcA, hcB, -⟩ := hP.setting
  have hc := _root_.GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl D θ A sA a hθ hcA hP.maj_eq
  have hb := _root_.GlobalTheory.Core.Rk.FockBox.isFockVec_delta D ψ θ A B sA sB hP.weil.std hθ Φ₁ Φ₂ h₁ h₂
  exact _root_.GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec D ψ θ (dblSp A) B 1 χB omh _ sB homh hθ hc.1 hcB (Khat A a) (isCompact_Khat A a) hc.2 _ hb

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EulerProductConjugationStableParametersPos
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerConjPos

open GlobalTheory.LFun GlobalTheory.LPositivity Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps (IsPosReal)

theorem lsd_pos : ∀ (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : GlobalTheory.LFun.Fam D.host.E) (μ : (AE D)ˣ →* Circle) (r : ℕ) (κ s : ℝ), IsHeckeChar D μ → ResEta D μ 0 → GlobalTheory.LFun.UnrOff (F := D.host.F) μ (S : Set (HeightOneSpectrum (𝓞 D.host.F))) → GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B r κ → κ + 1 < s → (∀ w ∉ GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F))), (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w ≠ w' → B w' = (B w).map star) ∧ (¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → (B w).map star = B w)) → ∃ l : ℝ, 0 < l ∧ GlobalTheory.LFun.LSD D S B μ (s : ℂ) = l := by
  intro D S B μ r κ s _ hb hμ hB hs hst
  classical
  have hc := isCMExt_host D
  have hb' := (resEta_iff μ 0).1 hb
  have hcv : Converges (above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (twist B (val μ)⁻¹) (s : ℂ) :=
    hB.converges_twist_val μ (by simpa using hs)
  have hpos : IsPosReal (LS (S : Set (HeightOneSpectrum (𝓞 D.host.F))) (twist B (val μ)⁻¹) (s : ℂ)) := by
    refine isPosReal_of_hasProd (hasProd_Lv hcv) hcv.ne_zero fun v => ?_
    have hnot : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v.1 →
        w ∉ above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F))) := fun w hw e => v.2 (hw ▸ e)
    have hlt : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v.1 →
        ∀ x ∈ twist B (val μ)⁻¹ w, ‖(x : ℂ) * npow w (-(s : ℂ))‖ < 1 := fun w hw =>
      norm_lt_one_of_bounded (hB.twist fun u _ => by simp [norm_val]) (by rw [Complex.ofReal_re]; linarith)
        (hnot w hw)
    have hun : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v.1 → UnrAt μ w := fun w hw =>
      hμ w (hnot w hw)
    by_cases hv : IsSplit (E := D.host.E) v.1
    · obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v.1 := by
        obtain ⟨P, -, -, hP, -⟩ := hv
        exact ⟨P, HeightOneSpectrum.ext hP⟩
      obtain ⟨w', hne, hall, hN, hN', -⟩ := SplitChart.exists_conj_place hc hw hv
      have hw' := (hall w').2 (Or.inr rfl)
      have e : Formalism.L2.Host.aboveF (L := D.host.E) D.host.F v.1 = {w, w'} := by ext u; simp [mem_aboveF, hall]
      have e2 : npow w' (-(s : ℂ)) = npow w (-(s : ℂ)) := by rw [npow, npow, hN, hN']
      have e3 : twist B (val μ)⁻¹ w' = (twist B (val μ)⁻¹ w).map star := by
        have hm := _root_.GlobalTheory.LFun.SplitVal.val_mul_val_eq_one _ _ _ hc μ 0 hb' w w' (hw.trans hw'.symm) hne (hun w hw) (hun w' hw')
        have hs' : (val μ w')⁻¹ = star (val μ w)⁻¹ := by
          rw [star_inv, star_eq_inv (norm_val μ w), inv_inv, eq_comm, eq_inv_iff_mul_eq_one, hm]
        simp only [twist, Pi.inv_apply, hs', Multiset.map_map, Function.comp_def, star_mul',
          (hst w (hnot w hw)).1 w' (hw'.trans hw.symm) hne]
      rw [Lv, e, Finset.prod_pair hne, locL, locL, e2, ← eulerFac_add]
      refine isPosReal_eulerFac (by
        rw [e3, Multiset.map_add (f := _), Multiset.map_map, add_comm]
        simp only [Function.comp_def, star_star, Multiset.map_id']) (star_npow _ _) fun x hx => ?_
      exact (Multiset.mem_add.1 hx).elim (hlt w hw x) (e2 ▸ hlt w' hw' x)
    · refine isPosReal_prod _ fun w hw => ?_
      have hw := mem_aboveF.1 hw
      have hi : IsInertAt D.host.F D.host.E v.1 w := hw ▸ (split_or_inert D w).resolve_left (hw ▸ hv)
      refine isPosReal_eulerFac ?_ (star_npow _ _) (hlt w hw)
      have hs' : star (val μ w)⁻¹ = (val μ w)⁻¹ := by
        rw [star_inv, star_eq_inv (norm_val μ w), inv_inv, eq_inv_iff_mul_eq_one, ← sq,
          GlobalTheory.T.sq_value_eq_one_at_inert_place_of_restrictsToQuadratic _ _ _ hc μ 0 hb' _ w hi (hun w hw)]
      have hBw := (hst w (hnot w hw)).2 (by rw [hw]; exact hv)
      conv_rhs => rw [twist, ← hBw]
      simp only [twist, Pi.inv_apply, hs', Multiset.map_map, Function.comp_def, star_mul']
  obtain ⟨l, hl, e⟩ := isPosReal_iff.1 hpos
  exact ⟨l, hl, e⟩

end GlobalTheory.EulerConjPos

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalSameDoubleCosetSumsZonal
section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.ZonalBorel

open GlobalTheory.PRep Formalism.UG

section Abstract

variable {G X V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup V] [Module ℂ V]

theorem exists_fixed_sum_eq {ρ : Representation ℂ G X} {π : Representation ℂ G V} (hρ : IsSmooth ρ)
    {K : Subgroup G} (hK : IsCompact (K : Set G)) (f : ρ.IntertwiningMap π) (hf : Function.Surjective f)
    (E : X →ₗ[ℂ] ℂ) (hE : ∀ u : X, (∀ x ∈ K, ρ x u = u) → E u = 0 → u = 0) {v : V} (hv : v ∈ fixed π K)
    (l : Module.Dual ℂ V) (hlv : l v = 1) :
    ∃ z : X, (∀ x ∈ K, ρ x z = z) ∧ E z = 1 ∧ ∀ S : Finset (G ⧸ K), (∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) →
      ∑ c ∈ S, l (π c.out v) = ∑ c ∈ S, E (ρ c.out z) := by
  obtain ⟨u, rfl⟩ := hf v
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK f.toLinearMap u fun h hh => by
    show f (ρ h u) = f u
    rw [f.isIntertwining]
    simpa using hv ⟨h, hh⟩
  have hw' : ∀ x ∈ K, ρ x w = w := fun x hx => by simpa using hw ⟨x, hx⟩
  have hfw' : f w = f u := hfw
  have hEw : E w ≠ 0 := fun h => by
    have h0 := hE w hw' h
    rw [h0, map_zero] at hfw'
    rw [← hfw', map_zero] at hlv
    exact zero_ne_one hlv
  refine ⟨(E w)⁻¹ • w, fun x hx => by rw [map_smul, hw' x hx], by simp [hEw], fun S hS => ?_⟩
  set z := (E w)⁻¹ • w with hz
  have hzK : ∀ x ∈ K, ρ x z = z := fun x hx => by rw [hz, map_smul, hw' x hx]
  have hEz : E z = 1 := by simp [hz, hEw]
  have hfz : f z = (E w)⁻¹ • f u := by rw [hz, map_smul, hfw']
  have h1 := hE (∑ c ∈ S, ρ c.out z - (∑ c ∈ S, E (ρ c.out z)) • z)
    (fun x hx => by rw [map_sub, Rep.sum_fixed ρ K hzK S hS x hx, map_smul, hzK x hx])
    (by rw [map_sub, map_sum, map_smul, hEz, smul_eq_mul, mul_one, sub_self])
  have h2 := congrArg (fun y => l (f y)) (sub_eq_zero.1 h1)
  have hI : ∀ c : G ⧸ K, f (ρ c.out z) = π c.out (f z) := fun c => f.isIntertwining _ _ _ _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hI, hfz, smul_eq_mul, hlv, mul_one] at h2
  rw [← Finset.mul_sum] at h2
  exact (mul_right_injective₀ (inv_ne_zero hEw)).eq_iff.1 (h2.trans (mul_comm _ _))

end Abstract

theorem exists_isBorelSph_hAct_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (α : Fin n → ℂˣ), HasSatake π α → ∀ ω : GL (Fin n) k → ℂ, IsZonal π (KO k (Fin n)) ω → ∃ φ : GL (Fin n) k → ℂ, IsBorelSph k (fun i : Fin n => (α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ ∧ ∀ g, Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) ω 1 = Formalism.UG.hAct (KO k (Fin n)) (Formalism.UG.dosetInd ℂ (KO k (Fin n)) g) φ 1 := by
  intro k _ _ _ _ n V _ _ π α ⟨_, _hs, S, f, hf⟩ ω ⟨v, hv, l, _hl, hlv, hω⟩
  have hsm : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, .id _, Function.surjective_id⟩ (isSmooth_parInd _ _)
  let E : S.toSubmodule →ₗ[ℂ] ℂ := ⟨⟨fun u => u.1.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have hr : ∀ u : S.toSubmodule, (∀ x ∈ KO k (Fin n), S.toRepresentation x u = u) →
      ∀ g, ∀ x ∈ KO k (Fin n), u.1.1.1 (g * x) = u.1.1.1 g := fun u h g x hx =>
    congrArg (fun z : S.toSubmodule => z.1.1.1 g) (h x hx)
  obtain ⟨z, hzK, hEz, key⟩ := exists_fixed_sum_eq hsm SplitFlip.isCompact_KO f hf E (fun u h h0 => by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    obtain ⟨b, hb, x, hx, rfl⟩ := iwasawa_blockTriangular k (Fin n) Fin.val g
    have h1 := parInd_law _ _ u.1 ⟨b, (mem_borel _).2 hb⟩ 1
    have h2 : u.1.1.1 1 = 0 := h0
    rw [h2, map_zero, smul_zero, mul_one] at h1
    exact (hr u h b x hx).trans h1) hv l hlv
  refine ⟨fun g => z.1.1.1 g, ⟨hr z hzK, fun b hb t ht => ?_⟩, fun g => ?_⟩
  · have h1 := Rep.law α z.1 b hb t ht 1
    have h2 : z.1.1.1 1 = 1 := hEz
    rwa [h2, mul_one, mul_one] at h1
  · have hK : IsCommensurated (KO k (Fin n)) :=
      PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact _ SplitFlip.isOpen_KO SplitFlip.isCompact_KO
    have hfin := Formalism.UG.P.finite_support_cosets hK (Formalism.UG.Final.DosetIndMem _ (KO k (Fin n)) ℂ g).2
    have hmem : ∀ c : GL (Fin n) k ⧸ KO k (Fin n), c ∈ hfin.toFinset ↔
        c.out ∈ DoubleCoset.doubleCoset g (KO k (Fin n) : Set (GL (Fin n) k)) (KO k (Fin n)) := fun c => by
      simp [dosetInd]
    have hT : ∀ x ∈ KO k (Fin n), ∀ c ∈ hfin.toFinset, x • c ∈ hfin.toFinset := by
      intro x hx c hc
      obtain ⟨a, ha, rfl⟩ := (GlobalTheory.ChainOnto.out_mem_doubleCoset_iff g c).1 ((hmem c).1 hc)
      refine (hmem _).2 ((GlobalTheory.ChainOnto.out_mem_doubleCoset_iff g _).2 ⟨x * a, mul_mem hx ha, ?_⟩)
      rw [mul_assoc]
      rfl
    have e : ∀ F : GL (Fin n) k → ℂ, hAct (KO k (Fin n)) (dosetInd ℂ (KO k (Fin n)) g) F 1 =
        ∑ c ∈ hfin.toFinset, F c.out := by
      intro F
      rw [hAct, finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
      · refine Finset.sum_congr rfl fun c hc => ?_
        rw [dosetInd, Set.indicator_of_mem ((hmem c).1 hc), one_mul, Pi.one_apply, one_smul]
      · intro c hc
        rw [Function.mem_support] at hc
        refine (hmem c).2 ?_
        by_contra h
        rw [dosetInd, Set.indicator_of_notMem h, zero_smul] at hc
        exact hc rfl
    rw [e, e]
    refine ((Finset.sum_congr rfl fun c _ => hω c.out).trans (key _ hT)).trans
      (Finset.sum_congr rfl fun c _ => ?_)
    show z.1.1.1 (1 * c.out) = _
    rw [one_mul]

end GlobalTheory.ZonalBorel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartsAtTwistPlacesChain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.TwistChart

variable {D : D7}

theorem isIdemOf_idem {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) :
    IsIdemOf φ (GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ)) := by
  refine ⟨GlobalTheory.EmbChart.isSplitIdem_idem _, ?_, GlobalTheory.SplitProjChart.rdA_idem φ⟩
  rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel]
  rfl

theorem exists_unif (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ ϖ : (Fv D.host.F v)ˣ, ValuativeRel.valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) =
      ValuativeRel.uniformizer (Fv D.host.F v) := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer (Fv D.host.F v))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact ValuativeRel.uniformizer_ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩

theorem unit_section {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) {e : AE D} (he : IsIdemOf φ e) :
    ∃ U : (Fv D.host.F v)ˣ →* (AE D)ˣ, (∀ y, (1 - e) * (U y : AE D) = 1 - e ∧ rdA φ (U y : AE D) = y) ∧
      ∀ (x : AE D) (y : (Fv D.host.F v)ˣ), (1 - e) * x = 1 - e → rdA φ x = y → x = U y := by
  have hπ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  have hee : e * e = e := he.1.1
  obtain ⟨sec, hsec⟩ : ∃ sec : Fv D.host.F v → AE D, ∀ y, rdA φ (sec y) = y :=
    ⟨fun y => (hπ.1 y).choose, fun y => (hπ.1 y).choose_spec⟩
  have hf1 : ∀ y, (1 - e) * ((1 - e) + e * sec y) = 1 - e := fun y => by
    linear_combination (1 - sec y) * hee
  have hf2 : ∀ y, rdA φ ((1 - e) + e * sec y) = y := fun y => by
    rw [map_add (f := _), map_sub, map_mul, map_one, he.2.2, hsec]; ring
  have key : ∀ x y, (1 - e) * x = 1 - e → rdA φ x = y → x = (1 - e) + e * sec y := by
    intro x y h1 h2
    have h3 : e * (x - sec y) = 0 := (hπ.2.1 _).1 (by rw [map_sub, h2, hsec, sub_self])
    have h4 : e * x = e * sec y := by rw [mul_sub] at h3; exact sub_eq_zero.1 h3
    calc x = (1 - e) * x + e * x := by ring
      _ = (1 - e) + e * sec y := by rw [h1, h4]
  have hmul : ∀ y z, (1 - e) + e * sec (y * z) = ((1 - e) + e * sec y) * ((1 - e) + e * sec z) := fun y z =>
    (key _ _ (by rw [← mul_assoc, hf1, hf1]) (by rw [map_mul, hf2, hf2])).symm
  have hone : (1 - e) + e * sec 1 = 1 := (key 1 1 (mul_one _) (map_one _)).symm
  let f : (Fv D.host.F v)ˣ → (AE D)ˣ := fun y =>
    ⟨(1 - e) + e * sec y, (1 - e) + e * sec ((y⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v),
      by rw [← hmul, Units.mul_inv, hone], by rw [← hmul, Units.inv_mul, hone]⟩
  exact ⟨MonoidHom.mk' f fun y z => Units.ext (by simp only [f, Units.val_mul]; exact hmul y z),
    fun y => ⟨hf1 y, hf2 y⟩, fun x y h1 h2 => key x y h1 h2⟩

end GlobalTheory.TwistChart

namespace GlobalTheory.TwistChart

variable {D : D7}

def blockEquiv (n r k t : ℕ) (h : n = r + k * t) : Fin r ⊕ Blocks k t ≃ Fin n :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sigmaEquivProd _ _).trans finProdFinEquiv)).trans
    (finSumFinEquiv.trans (finCongr h.symm))

theorem blockEquiv_inl (n r k t : ℕ) (h : n = r + k * t) (i : Fin r) : ((blockEquiv n r k t h (.inl i) : Fin n) : ℕ) = i := by
  simp [blockEquiv]

theorem exists_isChart (s : PiLocalization₂ D) (k : ℕ) (hrank : s.V.rank = D.R.r + k * D.R.t) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (φ : SplitProj D v) {e : AE D} (he : IsIdemOf φ e) : ∃ ι, IsChart s k φ ι := by
  have hπ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  have hJ := GlobalTheory.NoExcl.isHermND_gram s.V
  let ε := blockEquiv s.V.rank D.R.r k D.R.t hrank
  let re : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) ≃* GL (Fin s.V.rank) (Fv D.host.F v) :=
    Units.mapEquiv (Matrix.reindexAlgEquiv (Fv D.host.F v) (Fv D.host.F v) ε).toRingEquiv.toMulEquiv
  let L := GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) hJ (GlobalTheory.AdelicU.chartEmb hπ) (frCo φ s.β)
  let ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V :=
    (GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v).comp (L.symm.toMulEquiv.toMonoidHom.comp re.toMonoidHom)
  refine ⟨ι, ε, blockEquiv_inl _ _ _ _ hrank, fun y => ⟨?_, ?_⟩⟩
  · change GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v (ι y)) = ι y
    simp only [ι, MonoidHom.comp_apply, GlobalTheory.AdelicU.proj_emb_self]
  · have h1 : grpCo φ s.V (frCo φ s.β) (ι y) = GlobalTheory.SplitHecke.rho s.V (rdA φ) (frCo φ s.β) (ι y) := by
      refine Units.ext ?_
      rw [GlobalTheory.SplitHecke.rho_val]
      rfl
    rw [h1, GlobalTheory.AdelicU.rho_eq_splitEquivIn hπ s.V hJ]
    simp only [ι, L, MonoidHom.comp_apply, GlobalTheory.AdelicU.proj_emb_self]
    have h2 : L (L.symm (re y)) = re y := L.apply_symm_apply _
    change (L (L.symm (re y))).1.submatrix ε ε = y.1
    rw [h2]
    ext i j
    simp [re]

end GlobalTheory.TwistChart

namespace GlobalTheory.TwistChart

open GlobalTheory.ChainOnto GlobalTheory.ChainTw

theorem charts_at_twist : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, (∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP) ∧ ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → (∃ e, IsIdemOf φ e) ∧ (∃ x ϖ, IsLocUnif φ x ϖ) ∧ (∃ ι, IsChart s j φ ι) ∧ ∀ χ : (AE D)ˣ →* Circle, ∃ μ : (Fv D.host.F v)ˣ →* ℂˣ, GlobalTheory.SmGL.IsUnitaryChar μ ∧ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (χ x)) := by
  intro D c w hw j _ s hs PP hPP
  classical
  have hPg : PP ∈ c.Pg := by rw [hw.union]; exact Finset.mem_union_right _ hPP
  obtain ⟨-, ⟨es, hes, -⟩, -⟩ := hw.com.split
  refine ⟨?_, fun v φ _ => ?_⟩
  · obtain ⟨v, φ, -, h⟩ := (GlobalTheory.SplitIdemDict.idem_dictionary D).1 _ _ (hes PP hPg)
    exact ⟨v, φ, h⟩
  have he := isIdemOf_idem φ
  obtain ⟨U, hU1, hU2⟩ := unit_section φ he
  have huniq := (GlobalTheory.SplitProjChart.chart_rdA D v φ _ he).2.2.2.2
  obtain ⟨hr, -, hst⟩ := hs
  refine ⟨⟨_, he⟩, ?_, exists_isChart s j hst.rank φ he, fun χ => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := exists_unif (D := D) v
    exact ⟨U ϖ, ϖ, _, he, (hU1 ϖ).1, (hU1 ϖ).2, hϖ⟩
  · refine ⟨(Circle.toUnits.comp χ).comp U, fun y => ?_, fun x y ⟨e', he', h1, h2⟩ => ?_⟩
    · exact Circle.norm_coe _
    · obtain rfl := huniq e' he'
      have hx : x = U y := Units.ext (hU2 _ _ h1 h2)
      rw [hx]
      rfl

end GlobalTheory.TwistChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
section
namespace GlobalTheory

theorem weilRepresentationUnitaryPair : GlobalTheory.Published.WeilRepresentationUnitaryPair :=
  fun D ψ S T χS χT hψ hS hT rS rT =>
    GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT
      (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hS hT rS rT

end GlobalTheory
end

