module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0281
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0143
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0747
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0153
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
public import Formalism.LocalToGlobal.Divisibility.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0283
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicDatumRationalInvarianceOfKernelChain
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.RatPt

theorem isPtAd_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) ×
          GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp
  exact ⟨GlobalTheory.T.pointLattice_moved_rational_isometry A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp, GlobalTheory.T.chartPointFrames_move_rationalIsometry A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp,
    GlobalTheory.T.levelPrimeFunctionals_move_rationalIsometry A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp⟩

theorem xiPt_smul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m) β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG (E := t.X.E) (n := D.R.N (i + 1)) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi
  rcases lt_trichotomy i t.m2 with h | h | h
  · exact GlobalTheory.T.matrixStepDatum_equivariant_rational_unitary A dtU a hP hTie i hi h
  · exact GlobalTheory.T.firstCoupledStepDatum_rationalUnitary_equivariant A dtU a hP hTie i hi h
  · exact GlobalTheory.T.lastStepDatum_equivariant_rationalUnitary A dtU a hP hTie i hi h

theorem ratLaw_of_tie : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    PtEx A a → (∀ i hi, PtAway A a i hi) → RatLaw A a) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie hEx hAw
  intro i hi β β' x x' x₁ x₁' γ hγ γ' hγ' h₁ h₁' z
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.TwRat.ratUnitCol A dtU a hP hTie i (Nat.le_of_succ_le hi) γ hγ
  obtain ⟨g', hg'⟩ := _root_.GlobalTheory.TwRat.ratUnitCol A dtU a hP hTie (i + 1) hi γ' hγ'
  obtain ⟨p, hp⟩ := hEx i (Nat.le_of_succ_le hi) β x
  obtain ⟨p', hp'⟩ := hEx (i + 1) hi β' x'
  have hq := isPtAd_rat A dtU a hP hTie i (Nat.le_of_succ_le hi) β x x₁ γ hγ h₁ g hg p hp
  have hq' := isPtAd_rat A dtU a hP hTie (i + 1) hi β' x' x₁' γ' hγ' h₁' g' hg' p' hp'
  have hE1 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x₁' p' := ⟨⟨_, hq⟩, ⟨_, hq'⟩⟩
  have hE0 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' := ⟨⟨_, hp⟩, ⟨_, hp'⟩⟩
  have a1 := hAw i hi β β' x₁ x₁' x₁ x₁' _ _ _ _ hq hq' hE1.1.choose_spec hE1.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)
  have a0 := hAw i hi β β' x x' x x' _ _ _ _ hp hp' hE0.1.choose_spec hE0.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)
  unfold xiAd
  rw [dite_eq_left hE1, dite_eq_left hE0, a1, a0, _root_.GlobalTheory.TwV.seamHom_inFr_stdG A dtU a hP hTie i hi γ γ' g g' hg hg' z]
  rw [xiPt_smul A dtU a hP hTie i hi β β' x x' p p' hp hp' g g']

end GlobalTheory.RatPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobOpsIdx
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

noncomputable section

namespace GlobalTheory.FrobOpsIdx
open Polynomial

theorem frobOpsIdx : SphOps → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (Kw : Levels E a) (W0 : Set (HeightOneSpectrum (𝓞 E))), (∀ w ∈ W0, IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ Kw w = GlobalTheory.LFun.KGL w (n := a)) → ∃ (J : Type) (T : LocOps l ι Kw J) (x fr : J → G E Ω) (n : J → ℕ), (∀ j, x j = (fr j)⁻¹ ^ n j) ∧ (∀ j, T.pl j ∈ W0 ∧ ∃ A : ValuationSubring Ω, IsPlaceOver A (T.pl j) ∧ IsFrob A (normV (T.pl j)) (fr j)) ∧ (∀ w ∈ W0, ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s : G E Ω, IsFrob A (normV w) s → ∃ j, T.pl j = w ∧ fr j = s ∧ n j = 1) ∧ (∀ j g, ∃ q : ℚ, T.f j g = q) ∧ (∀ (j : J) (σ : SmIrr (GL (Fin a) ((T.pl j).adicCompletion E))), GlobalTheory.PRep.fixed σ.ρ (Kw (T.pl j)) ≠ ⊥ → ∀ B, GlobalTheory.LFun.HasSatGL (T.pl j) σ.ρ B → ∀ ρ : G E Ω →* GL (Fin a) (Qbar l), ((ρ (fr j)⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = ((UpperTheory.V.Af.algSat a (normV (T.pl j)) B).map fun b => Polynomial.X - Polynomial.C b).prod → ι.symm (T.z j σ) = trc ρ (x j)) ∧ ∀ w ∈ W0, ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), GlobalTheory.PRep.fixed σ.ρ (Kw w) ≠ ⊥ → ∀ B, GlobalTheory.LFun.HasSatGL w σ.ρ B → ∀ r : G E Ω →* GL (Fin a) (Qbar l), (∀ j (h : T.pl j = w), trc r (x j) = ι.symm (T.z j (h ▸ σ))) → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s : G E Ω, IsFrob A (normV w) s → ((r s⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = ((UpperTheory.V.Af.algSat a (normV w) B).map fun b => Polynomial.X - Polynomial.C b).prod := by
  intro hS E Ω _ _ _ _ _ _ l _ ι a Kw W0 hW
  classical
  have hl : l.Prime := Fact.out
  let J : Type := {p : HeightOneSpectrum (𝓞 E) × ValuationSubring Ω × G E Ω × ℕ //
    p.1 ∈ W0 ∧ IsPlaceOver p.2.1 p.1 ∧ IsFrob p.2.1 (normV p.1) p.2.2.1 ∧ 1 ≤ p.2.2.2}
  have hf : ∀ j : J, ∃ f : GL (Fin a) (j.1.1.adicCompletion E) →₀ ℂ,
      (∀ g, ∃ (m : ℤ) (e : ℕ), f g = (m : ℂ) / ((normV j.1.1 : ℕ) : ℂ) ^ e) ∧
      ∀ (σ : SmIrr (GL (Fin a) (j.1.1.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B →
        ∀ v ∈ PRep.fixed σ.ρ (GlobalTheory.LFun.KGL j.1.1 (n := a)),
          opOf σ.ρ f v = ((UpperTheory.V.Af.algSat a (normV j.1.1) B).map (· ^ ((j.1.2.2.2 : ℕ) : ℤ))).sum • v :=
    fun j => (hS E j.1.1 a).2 (j.1.2.2.2 : ℤ)
  let zz : ∀ j : J, SmIrr (GL (Fin a) (j.1.1.adicCompletion E)) → ℂ := fun j σ =>
    if h : ∃ B, GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B then
      ((UpperTheory.V.Af.algSat a (normV j.1.1) h.choose).map (· ^ j.1.2.2.2)).sum else 0
  have hz : ∀ (j : J) (σ : SmIrr (GL (Fin a) (j.1.1.adicCompletion E))) (B : Multiset ℂˣ),
      GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B → zz j σ = ((UpperTheory.V.Af.algSat a (normV j.1.1) B).map (· ^ j.1.2.2.2)).sum := by
    intro j σ B hB
    have h : ∃ B, GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B := ⟨B, hB⟩
    simp only [zz, dif_pos h]
    rw [show h.choose = B from h.choose_spec.unique hB]
  let T : LocOps l ι Kw J :=
    { pl := fun j => j.1.1
      split := fun j => (hW _ j.2.1).1
      away := fun j => (hW _ j.2.1).2.1
      f := fun j => (hf j).choose
      int := fun j g => by
        obtain ⟨m, e, he⟩ := (hf j).choose_spec.1 g
        rw [he]
        exact GlobalTheory.FrobOps.norm_le_one ι m _ e (GlobalTheory.FrobOps.not_dvd_normV hl _ (hW _ j.2.1).2.1)
      z := zz
      act := fun j σ v hv => by
        rw [(hW _ j.2.1).2.2] at hv
        by_cases h : ∃ B, GlobalTheory.LFun.HasSatGL j.1.1 σ.ρ B
        · obtain ⟨B, hB⟩ := h
          rw [hz j σ B hB, (hf j).choose_spec.2 σ B hB v hv]
          simp only [zpow_natCast]
        · have h0 : PRep.fixed σ.ρ (GlobalTheory.LFun.KGL j.1.1 (n := a)) = ⊥ := by
            by_contra hne
            exact h ((hS E j.1.1 a).1 σ hne)
          rw [h0, Submodule.mem_bot] at hv
          subst hv
          simp [opOf] }
  let fr : J → G E Ω := fun j => j.1.2.2.1
  let nn : J → ℕ := fun j => j.1.2.2.2
  let x : J → G E Ω := fun j => (fr j)⁻¹ ^ nn j
  refine ⟨J, T, x, fr, nn, fun j => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨j.2.1, j.1.2.1, j.2.2.1, j.2.2.2.1⟩
  · intro w hw A hA s hsF
    exact ⟨⟨(w, A, s, 1), hw, hA, hsF, le_rfl⟩, rfl, rfl, rfl⟩
  · intro j g
    obtain ⟨m, e, he⟩ := (hf j).choose_spec.1 g
    refine ⟨(m : ℚ) / ((normV j.1.1 : ℕ) : ℚ) ^ e, ?_⟩
    show (hf j).choose g = _
    rw [he]
    push_cast
    rfl
  · intro j σ _ B hB ρ hFE
    show ι.symm (zz j σ) = trc ρ (x j)
    rw [hz j σ B hB]
    apply ι.injective
    rw [RingEquiv.apply_symm_apply, GlobalTheory.FrobOps.iota_trc]
    exact (GlobalTheory.FrobOps.trace_pow_of_charpoly _ _ (by rw [Matrix.charpoly_map]; exact hFE) _).symm
  · intro w hw σ _ B hBσ r hr A hA s hsF
    rw [← Matrix.charpoly_map]
    refine GlobalTheory.CharpolyNewton.charpoly_eq_prod_of_trace_pow ℂ a _ _ ?_ ?_
    · simp [UpperTheory.V.Af.algSat, hBσ.card]
    · intro n hn
      let j : J := ⟨(w, A, s, n), hw, hA, hsF, hn⟩
      have h2 : trc r (x j) = ι.symm (zz j σ) := hr j rfl
      rw [hz j σ B hBσ] at h2
      rw [← GlobalTheory.FrobOps.iota_trc]
      change ι (trc r (x j)) = _
      rw [h2, RingEquiv.apply_symm_apply]

end GlobalTheory.FrobOpsIdx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelMovedPointFramesMatrixStepsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelMoved_point_frames_matrixSteps : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ j (hj : j < D.R.m), j ≤ t.m2 → ∀ (β : (St j hj.le).Ch) (x x₁ : UA D j hj.le) (κ : ((St j hj.le).K β).lev.U), x₁.1 = x.1 * κ.1 →
    ∀ p p₁, IsPtAd A a j hj.le β x p → IsPtAd A a j hj.le β x₁ p₁ →
    ∃ (k : GLQ t.X.E (D.R.N j) (SB t μ)) (c : SB t μ → t.X.Kˣ),
      (∀ P, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * ((k P)⁻¹).1) ∧
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG j (A.ib j hj β)) ((t.idx μ).levQ j (A.ib j hj β)) P (k P) (c P)) ∧
      ((((St j hj.le).K β).lev.chi κ : ℂˣ) : ℂ) = t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K) ∧
      ∀ P : SB t μ, IntAtA (F := D.host.F) (seamP t.seam P.1)
        (iA D.host.F D.host.E ((qOf (seamP t.seam P.1) : D.host.E))⁻¹ *
          ((((Matrix.GeneralLinearGroup.det κ.1)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
            iA D.host.F D.host.E (t.seam.iE ((LinearEquiv.det ((k P)⁻¹).1 : t.X.Eˣ) : t.X.E)) - 1))) := by
  first | exact @GlobalTheory.MatFrames.frames_mat | exact GlobalTheory.MatFrames.frames_mat | (intros; apply GlobalTheory.MatFrames.frames_mat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpTwOneNe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory

theorem WeilDeligne.WD.lpTw_one_ne {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (x : WD h) : 0 < x.lpDim → x.lpTw 1 ≠ x := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  intro hn heq
  rw [WD.lpTw_mk, WD.mk_eq_mk] at heq
  obtain ⟨e, he, -⟩ := heq
  rw [WD.lpDim_mk, Module.finrank_fin_fun] at hn
  set σ := frob h
  set T := (a.tw 1).ρ σ
  set B := a.ρ σ
  have hconj : (e : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ T ∘ₗ (e.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = B := by
    refine LinearMap.ext fun v => ?_
    show e ((a.tw 1).ρ σ (e.symm v)) = a.ρ σ v
    rw [he, LinearEquiv.apply_symm_apply]
  have hdet : LinearMap.det T = LinearMap.det B := by
    rw [← hconj, LinearMap.det_conj]
  have hT : T = ((normV w : ℕ) : ℂ) • B := by
    show (a.tw 1).ρ σ = _
    rw [WDRep.tw_ρ, deg_frob]
    simp only [Complex.ofReal_one, Complex.cpow_one, zpow_one]
    rfl
  rw [hT, LinearMap.det_smul, Module.finrank_fin_fun] at hdet
  have hB : LinearMap.det B ≠ 0 := by
    intro h0
    have h1 : B * a.ρ σ⁻¹ = 1 := by
      show a.ρ σ * a.ρ σ⁻¹ = 1
      rw [← map_mul, mul_inv_cancel, map_one]
    have := congrArg LinearMap.det h1
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have hq : ((normV w : ℕ) : ℂ) ^ n = 1 := by
    have := mul_right_cancel₀ hB (hdet.trans (one_mul _).symm)
    exact this
  have hq' : (normV w : ℕ) ^ n = 1 := by exact_mod_cast hq
  have h1q := one_lt_normV w
  have : 1 < (normV w : ℕ) ^ n := Nat.one_lt_pow hn.ne' h1q
  omega

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMono0LpCharLpSp
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.SegLen

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem tmul_ne_zero_of_ne {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] {x : X} {y : Y}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Y, φ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)
  intro h0
  have := congrArg ((TensorProduct.rid ℂ X).toLinearMap ∘ₗ LinearMap.lTensor X φ) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
    map_zero] at this
  exact hx ((smul_eq_zero.1 this).resolve_left hφ)

theorem lpChar_lpSp_one' (x : WD h) : x.lpChar (WD.lpSp (h := h) 1) = x := by
  have h1 : WD.lpSp (h := h) 1 = WD.lpOfChar h (WeilDeligne.unrChar h (qPow w 0)) (isSmooth_unrChar h _) := by
    refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩
    · funext i
      simp [WDRep.spEig]
    · funext i
      simp [shiftEnd_apply]
  rw [h1, lpChar_lpOfChar]
  exact WD.lpTw_zero x

theorem not_mono0_lpChar_lpSp {x : WD h} (hx : IsIrrWD x) {n : ℕ} (hn : 2 ≤ n) :
    ¬ (x.lpChar (WD.lpSp (h := h) n)).mono0 := by
  have h0 := TemperedRec.monodromy_zero_of_irreducible_weilDeligne E Ω A w h x hx
  obtain ⟨m, b, rfl, hirr⟩ := hx
  have : Nontrivial (Fin m → ℂ) := Model.nontrivial_of_isIrreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin m → ℂ)
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
  rw [WD.lpSp, WD.lpChar_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tensor_N, h0, WDRep.sp_N, LinearMap.rTensor_zero, zero_add]
  intro hN
  obtain ⟨u, hu⟩ : ∃ u, shiftEnd n u ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact shiftEnd_ne_zero hn (LinearMap.ext hc)
  have := LinearMap.congr_fun hN (v ⊗ₜ u)
  rw [LinearMap.lTensor_tmul, LinearMap.zero_apply] at this
  exact tmul_ne_zero_of_ne hv hu this

end GlobalTheory.SegLen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodValuationBoundTypePrimePlaceOfChainAgreeme
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound GlobalTheory.ColPeriod

namespace GlobalTheory.ColPeriodTies

theorem boundAt_of_chainTie (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D)
    (Ch : Chars (recFields D) (recPrimes EX) D.R.m) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
    (eta : Formalism.L2.Host.HChar D.host.E) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
    {δ : ℂ} (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (C1 : ℝ)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.Integrality) (hJ : JetLossAll D EX sel B χ cD) (hC : 1 ≤ C1)
    (hH : HostTie EX) (hCT : CharTie Ch mu0 eta sel) (hA : AnTie D δ χ cD) (i : Fin 2) (hS : SizeAt D i)
    (w : LiftErrorLocal.Pl D) (hw : LiftErrorLocal.Over D i w) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (hCh : ChainTie Ch sel Dx mu0 (ambOf (recSeam D) B χ cD) u μ) :
    BoundAt L EX C1 i w u μ := by
  classical
  obtain ⟨-, hTied, -, hsel⟩ := hCT
  obtain ⟨ξ, cst, I, hI, b, hY, hK, hF, hP, eM, jA, -, -, hrat, hcol, hrow, hper⟩ := hCh
  rintro φ hφ F ⟨c, hc⟩
  have hX := hH.2.2.2.1.ok
  have hPr := hH.2.2.2.2
  obtain ⟨hne, hloss⟩ := vG_loss_le L EX hPr i w hw u
  choose! x hx using hrow.2.2.1
  have hxF : jA (∑ v ∈ (D.what₂.Mtilde μ).gen, D.what₂.OtoLL (c v) • x v) = F := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc, map_sum]
    exact Finset.sum_congr rfl fun v hv => by rw [LinearMap.map_smulₛₗ, hx v hv]; rfl
  have hxM := (hrow.2.2.2 _).2 ⟨fun v => ⟨D.what₂.OtoLL (c v), D.O_int _⟩, hxF.trans hc⟩
  refine ⟨_, (hxF ▸ hper φ _).symm, ?_⟩
  have hw' : D.what₂.places.resChar w = D.host.g i := hw
  have hg : ((D.host.g i : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
    refine mem_of_vAdd_pos _ ?_
    have h1 := D.what₂.places.val_resChar w
    rw [hw', D.val_eq w _ (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero)] at h1
    have h2 : vAdd (D.plEq w) (D.host.g i : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by exact_mod_cast h1
    have h3 : (((D.host.g i : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = (D.host.g i : D.what₂.LL) := map_natCast (algebraMap _ _) _
    rw [h3, h2]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hTS : (recPrimes EX).T u ∈ badS D := Or.inr (Or.inl ⟨u, rfl⟩)
  have hgS : ∀ k, (recPrimes EX).g k ∈ badS D := fun k => by
    fin_cases k <;> simp [badS, hostS]
  have hb : 2 * (recFields D).f * D.R.N D.R.m + 1 < D.host.g i := by
    rw [show (recFields D).f = D.R.f from D.what₂.card_Tau]
    exact hS.1
  have hdeg : ∀ j < D.R.m, (∑ τ, ∑ a, ((recWts EX).nuW u (j + 1) τ).w a) + 1 < (D.host.g i : ℤ) := by
    intro j hj
    have h1 := (hS.2 u (j + 1) (Finset.mem_Icc.2 ⟨by omega, hj⟩)).1
    have h2 : LiftErrorLocal.Dpi D u (j + 1) = ((∑ τ, ∑ a, ((recWts EX).nuW u (j + 1) τ).w a : ℤ) : ℝ) := by
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl fun τ _ => partitionSize D EX u j hj τ
    have h3 := Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => sum_nuW_nonneg (Pr := recPrimes EX) (recWts EX) u hj τ
    rw [h2] at h1
    have h4 : 2 * (∑ τ, ∑ a, ((recWts EX).nuW u (j + 1) τ).w a) + 2 < (D.host.g i : ℤ) := by exact_mod_cast h1
    omega
  have hcolb := colMu_bound_all (recWts EX) Ch sel ξ cst I _ (hJ hH hsel hA) GlobalTheory.JetOpWeylLat.jetOpWeyl chainWeights stdMove levelPrimes
    (scalarUnit_of levelPrimes heckeUnit twistUnit) entryAtG (EntQ.entryAtQ volumeAtQ) TopTwist.topAtQ hX hPr hsel u hTS hgS hI
    hTied b hY (Formalism.L2.Col.rPsymF Ch) hK hF i (D.plEq w) hg
    (fun j hj b' => wtUnit_chF (recWts EX) sel ξ I hX u hF (hPr.g_prime i) hb _ hg hj b') hdeg hrat _ ((hcol φ).1 hφ)
  have hm := GlobalTheory.BranchMembers.members _ _ _ (recWts EX) (recWts_ok EX) u
  have hval := valuation_PtilE_le_one (recWts EX) Ch sel ξ hX hPr hsel u hTS (hB _ _ _ _ _ _ _) (fun τ => (hm τ).1)
    (fun τ => (hm τ).2) (Formalism.L2.Col.rPsymF Ch) hP (hPr.g_prime i) (hPr.T_ne_g u i) hb (D.plEq w) hg
    ((∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) • _) hcolb _ hxM
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at hval
  suffices key : ∀ y : D.what₂.LL, (D.plEq w).valuation D.what₂.LL
      ((∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) * y) ≤ 1 →
      y = 0 ∨ -(∑ j ∈ LiftErrorLocal.lifts D, vNN EX i u j w) - C1 * LiftErrorLocal.errC D L ≤ LiftErrorLocal.vG D w y from key _ hval
  intro y hval
  by_cases hy : y = 0
  · exact Or.inl hy
  right
  have hc0 := Finset.prod_ne_zero_iff.2 fun j (_ : j ∈ Finset.range D.R.m) => hne j
  have h1 := vAdd_nonneg_of_le _ (mul_ne_zero hc0 hy) hval
  rw [vAdd_mul_of_ne _ hc0 hy] at h1
  have he : (0 : ℝ) < D.what₂.places.ramIdx w := by exact_mod_cast D.what₂.places.ramIdx_pos w
  have h2 : 0 ≤ LiftErrorLocal.vG D w (∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) + LiftErrorLocal.vG D w y := by
    unfold LiftErrorLocal.vG
    rw [← add_div]
    exact div_nonneg (by exact_mod_cast h1) he.le
  have h3 : 0 ≤ LiftErrorLocal.errC D L := by
    have := L.etaSz_pos.le
    unfold LiftErrorLocal.errC
    positivity
  nlinarith

theorem boundAt_of_ties : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D) (μ : D.what₂.Tup),
    TiesAt D EX Dx μ → ∀ i : Fin 2, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i → ∀ w, LiftErrorLocal.Over D i w → ∀ u : D.what₂.Word,
      D.what₂.places.resChar w ≠ (D.mem u).A.T → GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.BoundAt L EX 1 i w u μ := by
  intro hJS D L EX Dx μ ⟨Ch, mu0, eta, sel, δ, B, χ, cD, hH, hCT, hA, hCh⟩ i hS w hw u _
  have hJ : JetLossAll D EX sel B χ cD := GlobalTheory.T.thetaJetIntegrality_typePrime_of_splitTableBound hJS D EX sel δ B χ cD
  exact boundAt_of_chainTie D L EX Dx Ch mu0 eta sel B χ cD 1
    (GlobalTheory.BranchFormula.integrality Formalism.L2.DIV.BrJ.branching_interlacing_pairs) hJ le_rfl
    hH hCT hA i hS w hw u μ (hCh u)

end GlobalTheory.ColPeriodTies

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEqZeroOffSubgroupOfSelfTwistStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_eq_zero_off_subgroup_of_selfTwist : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] [IsGalois K M], (Module.finrank K M).Prime → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub K a) (r : G K Ω →* GL (Fin a) (Qbar l)), Weak π ι r → ∀ η : HChar K, UpperTheory.V.Published.IsNormChar M η → UpperTheory.V.Published.SelfTw (CG.mk π).HasSat η → ∀ g : G K Ω, (∃ x : M, g (algebraMap M Ω x) ≠ algebraMap M Ω x) → (r g).val.trace = 0 := by
  first | (exact @GlobalTheory.SelfTwWeak.trace_eq_zero_of_selfTw) | (exact GlobalTheory.SelfTwWeak.trace_eq_zero_of_selfTw) | (intros; apply GlobalTheory.SelfTwWeak.trace_eq_zero_of_selfTw  <;> assumption)
end

