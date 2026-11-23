module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.Bundle0005
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsStandardBasesLatticeAtPlaceOfAdaptedBases
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0083
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleKernelSeriesInertPrimeNonConjugateFrob
section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem exists_beFam_evenConditionsInert_of_kerEnt : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∃ ep be, BeFam D ep be ∧ OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be (fun _ _ => -1)) Y := by
  intro hAlg hHost D L hT Gi Gl K Y cX ex t hHyp hAd h3
  have hOrb := (Formalism.MainNotions.DIV.Inh.orbit_admissible_of_split_bound D h3).1
  have key : ∀ w : D.what₂.places.Pl, ∃ (e : ℂ_[D.what₂.places.resChar w])
      (b : MvPowerSeries (ZMod (nP D (D.what₂.places.resChar w))) ℂ_[D.what₂.places.resChar w]),
      ((IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)) →
      ‖e‖ = 1 ∧ BeStd (D.what₂.places.resChar w) (nP D (D.what₂.places.resChar w)) b ∧
      ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
        (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E),
        admitted D N N' L L' → StdBases D (t.ent.lam w) L P → StdBases D (t.ent.lam w) L' P' →
        ∀ G, IsComb D t.B.tor (t.B.eNat t.χ) (t.ent.lam w) L L' G → ∀ R, OrbitPlaces.IsReps D (D.what₂.places.resChar w) R →
          OrbitPlaces.ThetaExpansionAllPlaces D (D.what₂.places.resChar w) R e (fun _ => -1) (fun _ => b) (stdSer D (t.ent.lam w) (fun _ => 1) P P' G) := by
    intro w
    by_cases hc : (IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)
    · have hO := hOrb _ (D.what₂.places.resChar_prime w) hc
      have hH := hHost D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (D.what₂.places.resChar w) (t.ent.lam w) hO.five
        (hc.imp_left And.left)
      obtain ⟨e, b, he, hb, hB⟩ := _root_.GlobalTheory.KerStd.normalisedFamily_standardBases_integrality D t.cc t.δ t.B t.χ _ (t.ent.lam w) hH hO (hc.imp_left (And.imp_right HEv.ne_zero))
      exact ⟨e, b, fun _ => ⟨he, hb, hB⟩⟩
    · exact ⟨1, 0, fun h => absurd h hc⟩
  choose ep be hbe using key
  refine ⟨ep, fun w _ => be w, ?_, ?_⟩
  · intro w hc
    obtain ⟨he, hb, -⟩ := hbe w hc
    exact ⟨he, fun _ => hb⟩
  · intro u μ w hLev hc R hR
    obtain ⟨he, hb, hB⟩ := hbe w hc
    have hO := hOrb _ (D.what₂.places.resChar_prime w) hc
    refine ⟨⟨he, fun _ _ => Or.inr rfl, fun _ _ => _root_.GlobalTheory.KerStd.bHyps_of_beStd _ _ _ hO.five hO.two hO.even hb⟩, ?_⟩
    intro i hi _ c c'
    have hAdPl : Formalism.L2.Ker.AdPl D w := by
      rcases hc with h | h
      · exact Or.inl h.1
      · exact Or.inr (Or.inl h)
    obtain ⟨Pm, hBas, -, hConj, hTh⟩ := hAd w hAdPl u μ hLev
    have hcomb := GlobalTheory.Ggeo.KerComb.comb_of_tied hAlg D L hT Gi Gl K Y cX ex t hHyp u μ w hLev i hi c c'
    have hS : ∀ j, j ≤ D.R.m → ∀ c, StdBases D (t.ent.lam w) ((t.O u μ).lat j c).1 (Pm j c) := fun j hj c =>
      _root_.GlobalTheory.KerStd.stdBases_of_basR D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat j c).2.1 (fun τ => hBas j hj c τ)
        (fun τ τ' h => hConj j hj c τ τ' h)
    show OrbitPlaces.ThetaExpansionAllPlaces D _ R (ep w) (fun _ => -1) (fun _ => be w) (t.ent.Th u μ w i c c')
    rw [hTh i hi c c', _root_.GlobalTheory.atLin_adCoef_eq_stdSer]
    exact hB _ _ _ _ _ _ hcomb.1 (hS i hi.le c) (hS (i + 1) hi c') _ hcomb.2 R hR

end GlobalTheory.KerStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCGal

open Formalism.MainNotions.SumRepresentations.At GlobalTheory.TwistLG

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a b : ℕ}

theorem sumRep_val (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl

theorem cont_sumRep [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k]
    (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k)
    (c : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (c' : Continuous fun g => ((ρ' g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) :
    Continuous fun g => ((sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) := by
  simp only [sumRep_val]
  exact (c.matrix_fromBlocks continuous_const continuous_const c').matrix_reindex _ _

theorem ss_sumRep (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (h : IsSSRep ρ) (h' : IsSSRep ρ') :
    IsSSRep (sumRep ρ ρ') := by
  refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod ((LinearEquiv.funCongrLeft k k finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) h h'
  rw [sumRep_val]
  ext i <;>
    simp [Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft]
  all_goals rfl

theorem ss_zero (ρ : Γ →* GL (Fin 0) k) : IsSSRep ρ := fun W _ =>
  ⟨⊥, fun g v hv => by simp [Subsingleton.elim v 0], by rw [Subsingleton.elim W ⊤]; exact isCompl_top_bot⟩

end Rep

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem eq_lpZero {w : PlE H} (x : A.LP w) (hu : A.unr x) (hd : A.lpDim x = 0) : x = A.lpZero w := by
  have h1 : A.frobEig x = 0 := Multiset.card_eq_zero.1 (by rw [A.frobEig_card _ hu, hd])
  have h2 := A.unr_eq_lpUnr _ (A.lpZero_unr w)
  rw [A.frobEig_zero] at h2
  rw [A.unr_eq_lpUnr _ hu, h1, h2]

theorem lpTw_lpZero (w : PlE H) (c : ℝ) : A.lpTw (A.lpZero w) c = A.lpZero w :=
  eq_lpZero N A _ ((A.unr_tw _ _).2 (A.lpZero_unr w)) (by rw [A.lpDim_tw, A.lpDim_zero])

theorem param_int (hLP : TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) (u t : ℝ) :
    A.lpChar (A.lpChar (A.lpTw (A.locG π w) u) (A.lpTw (A.locG A.etaT w) (1 / 2)))
      (A.lpTw (A.locG A.etaTinv w) (t - 1 / 2)) = A.lpTw (A.locG π w) (u + t) := by
  have d1 : A.lpDim (A.locG A.etaT w) = 1 := A.locG_dim _ w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  set X := A.lpTw (A.locG π w) u
  have c3a := (hLP w (A.lpChar X (A.lpTw (A.locG A.etaT w) (1 / 2))) (A.lpZero w) (A.locG A.etaTinv w)
    (A.locG A.etaTinv w) (t - 1 / 2) d2 d2).2.2.1
  have c3b := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaT w) (1 / 2) d1 d1).2.2.1
  have c2 := (hLP w (A.lpChar X (A.locG A.etaT w)) (A.lpZero w) (A.locG A.etaTinv w) (A.locG A.etaTinv w)
    (1 / 2) d2 d2).2.1
  have c4 := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.1
  have c5 := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.2.1
  rw [c3a, c3b, c2, c4, etaT_char_etaTinv N A w, c5, A.lpTw_add, A.lpTw_add]
  congr 1
  ring

end Glob

section Piece

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem eta_alg (hAut : TieAut N A) (m : ℤ) (τ : H.E →+* ℂ) :
    (∀ z ∈ A.infG A.etaT τ, ∃ k : ℤ, z + (((m : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ)) ∧
    (∀ z ∈ A.infG A.etaTinv τ, ∃ k : ℤ, z + (((m : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ)) := by
  obtain ⟨h1, h2⟩ := hAut.2.1 τ
  rw [h2]
  rcases h1 with h1 | h1 <;> rw [h1] <;> refine ⟨fun z hz => ?_, fun z hz => ?_⟩ <;>
    simp only [Multiset.map_singleton, Multiset.mem_singleton] at hz <;> subst hz
  · exact ⟨m + 1, by push_cast; ring⟩
  · exact ⟨m, by push_cast; ring⟩
  · exact ⟨m, by push_cast; ring⟩
  · exact ⟨m + 1, by push_cast; ring⟩

end Piece

section List

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

end List

end GlobalTheory.BCGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlocksLtOfParabolicUnipotentRadicalNeBot
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.UnipRadProper

theorem blocks_lt_of_unipRad_ne_bot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad k e ≠ ⊥ → ∀ a, d a < n := by
  intro k _ _ _ _ n s d e h a
  by_contra hle
  push_neg at hle
  apply h
  have hcard : ∑ b, d b = n := by simpa using (Fintype.card_congr e)
  have hzero : ∀ b, b ≠ a → d b = 0 := by
    intro b hb
    have h2 : d a + d b ≤ ∑ c, d c :=
      Finset.add_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a) (Finset.mem_univ b) (Ne.symm hb)
    omega
  have hblk : ∀ (b : Fin s) (j : Fin (d b)), b = a := by
    intro b j
    by_contra hb
    exact (hzero b hb ▸ j).elim0
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  ext i j
  obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨c, j⟩, rfl⟩ := e.surjective j
  obtain rfl := hblk b i
  obtain rfl := hblk c j
  rw [(mem_unipRad.1 hg).2]
  simp [Matrix.one_apply]

end GlobalTheory.UnipRadProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjSPV
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut

namespace GlobalTheory.TypeTame

noncomputable abbrev conjSP {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) : SplitPlace L :=
  ⟨s.v, s.i.comp (IsCMField.complexConj L).toAlgHom⟩

theorem conjSP_i {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (x : L) :
    (conjSP s).i x = s.i (IsCMField.complexConj L x) := rfl

end GlobalTheory.TypeTame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalJacquetSubquotientAtMostOneNonemptyBlock
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SmGL.CuspRow

theorem block_unique_of_isCuspidal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (s' : ℕ) (b : Fin s' → ℕ) (f : (Σ j, Fin (b j)) ≃ Fin d) (X : Fin s' → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (Fin (b j)) k) (X j)), GlobalTheory.SmGL.IsCuspidal σ → (∀ j, Nontrivial (X j)) → GlobalTheory.SmGL.IsSubquotient (GlobalTheory.SmGL.piTensor ρ) (GlobalTheory.SmGL.jac f σ) → ∀ j j', 0 < b j → 0 < b j' → j = j' := by
  intro k _ _ _ _ d V _ _ σ s' b f X _ _ ρ hσ hX hsub j j' hj hj'
  by_contra hne
  have hU : GlobalTheory.SmGL.unipRad k f ≠ ⊥ := by
    refine GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.2 ?_
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨f ⟨j, ⟨0, hj⟩⟩, f ⟨j', ⟨0, hj'⟩⟩, by rwa [GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]⟩
    · exact ⟨f ⟨j', ⟨0, hj'⟩⟩, f ⟨j, ⟨0, hj⟩⟩, by rwa [GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]⟩
  have hs := hσ.2 s' b f hU
  have hn := GlobalTheory.ProdSupport.nontrivial_piTensor X hX
  obtain ⟨S, g, hg⟩ := hsub
  have hS : Subsingleton S.toSubmodule := inferInstance
  exact not_subsingleton _ (Function.Surjective.subsingleton hg)

end GlobalTheory.SmGL.CuspRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwistBridgeDR

open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.TwistAbove

theorem twGL_eq {Γ K : Type} [Group Γ] [CommRing K] {a : ℕ} (r : Γ →* GL (Fin a) K) (μ : Γ →* Kˣ) :
    Formalism.MainNotions.SumRepresentations.At.twGL r μ = GlobalTheory.TwistAbove.twGL μ r := by
  ext g i j
  simp [Formalism.MainNotions.SumRepresentations.At.twGL, GlobalTheory.TwistAbove.twGL, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]

theorem characterAsRankOneRep_det_comp {Γ K : Type} [Group Γ] [CommRing K] (c : Γ →* GL (Fin 1) K) :
    GlobalTheory.TripleGal.rk1 (Matrix.GeneralLinearGroup.det.comp c) = c := by
  ext g i j
  fin_cases i; fin_cases j
  simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a : ℕ}

theorem repE_twGL' {L : FinExt l} (χ : ↥Gw →* (↥L.1)ˣ) (s : ↥Gw →* GL (Fin a) ↥L.1)
    (g : ↥(GK Bw.Kw)) (x : Fin a → ↥L.1) :
    Bw.repE L (GlobalTheory.TwistAbove.twGL χ s) g x = ((χ (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) • Bw.repE L s g x := by
  change Matrix.toLin' ((GlobalTheory.TwistAbove.twGL χ s (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x =
    ((χ (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) •
      Matrix.toLin' ((s (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x
  rw [twGL_val, Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact Matrix.smul_mulVec _ _ _

theorem isModel_untwist {L : FinExt l} {r : ↥Gw →* GL (Fin a) (Om l)} {c : ↥Gw →* GL (Fin 1) (Om l)}
    {t : ↥Gw →* GL (Fin a) ↥L.1} {cc : ↥Gw →* GL (Fin 1) ↥L.1}
    (mt : IsModel Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) L t)
    (mc : IsModel Bw c L cc) : IsModel Bw r L (GlobalTheory.TwistAbove.twGL (chr cc)⁻¹ t) := by
  refine ⟨mt.1, ?_⟩
  ext g i j
  have e1 := congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) =>
    ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) mt.2
  have e2 := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) =>
    ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) mc.2
  rw [twGL_eq] at e1
  simp only [mapRep] at e1 e2 ⊢
  simp [Matrix.det_unique] at e1 e2 ⊢
  have hne : ((c g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0 ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det (c g)).ne_zero
    simpa [Matrix.det_unique] using this
  rw [e1, e2, inv_mul_cancel_left₀ hne]

theorem isdRAt_twist_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Loc.Om l)) (c : ↥Gw →* GL (Fin 1) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → Continuous (fun g => ((c g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l))) → GlobalTheory.Pst.IsdRAt P Bw c → (GlobalTheory.Pst.IsdRAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) ↔ GlobalTheory.Pst.IsdRAt P Bw r) := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw a r c _ _ hc
  obtain ⟨T⟩ := hT
  obtain ⟨L₂, c₂, m₂, d₂⟩ := hc
  constructor
  · rintro ⟨L₁, t₁, m₁, d₁⟩
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    have mt := m₁.enlarge l₁
    have mc := m₂.enlarge l₂
    have dt := (local_ext P Bw l₁ t₁).2.1.2 d₁
    have dc := (local_ext P Bw l₂ c₂).2.1.2 d₂
    set t := mapRep (IntermediateField.inclusion l₁).toRingHom t₁
    set cc := mapRep (IntermediateField.inclusion l₂).toRingHom c₂
    refine ⟨_, _, isModel_untwist Bw mt mc, ?_⟩
    have hν := repE_rank_one Bw cc
    have hρ : ∀ g x, Bw.repE (supExt L₁ L₂) t g x =
        ((chr cc (Bw.e.symm g) : (↥(supExt L₁ L₂).1)ˣ) : ↥(supExt L₁ L₂).1) •
          Bw.repE (supExt L₁ L₂) (GlobalTheory.TwistAbove.twGL (chr cc)⁻¹ t) g x := by
      intro g x
      rw [repE_twGL', smul_smul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        one_smul]
    rw [← isDR_iff] at dt dc ⊢
    exact (GlobalTheory.TwistDR.isDR_twist_iff l P AI T Bw.Kw (supExt L₁ L₂) (Fin a → ↥(supExt L₁ L₂).1)
      _ _ _ _ hν hρ dc).2 dt
  · rintro ⟨L₁, r₁, m₁, d₁⟩
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    have mc : IsModel Bw (GlobalTheory.TripleGal.rk1 (Matrix.GeneralLinearGroup.det.comp c)) (supExt L₁ L₂)
        (mapRep (IntermediateField.inclusion l₂).toRingHom c₂) := by
      rw [characterAsRankOneRep_det_comp]; exact m₂.enlarge l₂
    refine ⟨_, _, isModel_twGL Bw (r' := Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c))
      (μ := Matrix.GeneralLinearGroup.det.comp c) (fun g => by rw [twGL_eq]; exact twGL_val _ _ _)
      (m₁.enlarge l₁) mc, (twist_common Bw _ _ T).1 ((local_ext P Bw l₁ r₁).2.1.2 d₁)
        ((local_ext P Bw l₂ c₂).2.1.2 d₂)⟩

end GlobalTheory.TwistBridgeDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.DeRhamRead
open Formalism.BasicNotions.Loc

theorem exists_model_of_mem {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {a : ℕ}
    (r : Γ →* GL (Fin a) (Om l)) (hr : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l)))) (L : FinExt l)
    (hL : ∀ g i j, (r g : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) :
    ∃ ρ : Γ →* GL (Fin a) ↥L.1, Continuous (fun g => (ρ g : Matrix (Fin a) (Fin a) ↥L.1)) ∧
      mapRep (algebraMap ↥L.1 (Om l)) ρ = r := by
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  let M : Γ → Matrix (Fin a) (Fin a) ↥L.1 :=
    fun g => Matrix.of fun i j => ⟨(r g : Matrix (Fin a) (Fin a) (Om l)) i j, hL g i j⟩
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin a) (Fin a) ↥L.1 →+* Matrix (Fin a) (Fin a) (Om l)) :=
    fun A B h => Matrix.ext fun i j => f.injective (by simpa using congrFun (congrFun h i) j)
  have hM : ∀ g, f.mapMatrix (M g) = (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => Matrix.ext fun i j => rfl
  let ρ : Γ →* GL (Fin a) ↥L.1 :=
    { toFun := fun g => ⟨M g, M g⁻¹,
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
      map_one' := Units.ext (hinj (by rw [hM, map_one, Units.val_one, Units.val_one, map_one]))
      map_mul' := fun g h => Units.ext (hinj (by
        show f.mapMatrix (M (g * h)) = f.mapMatrix (M g * M h)
        rw [map_mul, hM, hM, hM, map_mul, Units.val_mul])) }
  refine ⟨ρ, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_induced_rng.2 ((continuous_apply j).comp ((continuous_apply i).comp hr))
  · exact MonoidHom.ext fun g => Units.ext (hM g)

theorem isdRW_iff_isdRAt : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → ∀ (a : ℕ) (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → (W.IsdRW l ι r w ↔ GlobalTheory.Pst.IsdRAt (D.loc l) Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 r w)) := by
  intro D T W l _ ι w hw O _ _ _ B hj a r hr
  obtain ⟨LL', hL, hmem⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G D.host.E D.nd.Om) a r hr B.LL
  obtain ⟨r₁, c₁, rfl⟩ := exists_model_of_mem r hr LL' hmem
  obtain ⟨-, H⟩ := W.loc l ι w hw _ B hj ((algebraMap ↥B.LL.1 (Om l)).comp B.toLL) (fun _ => rfl)
  have hm : GlobalTheory.Pst.IsModel B (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (algebraMap ↥LL'.1 (Qbar l)) r₁) w) LL'
      (r₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := ⟨hL, rfl⟩
  exact (H LL' hL a r₁ c₁).2.1.trans (hm.isdRAt_iff (D.loc l)).symm

end GlobalTheory.DeRhamRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsContinuousLadicGalRepModelFiniteExtHost
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompactRepField

theorem exists_hom_of_entries_mem {F E Γ : Type} [Field F] [Field E] [Algebra F E] [Group Γ]
    {a : ℕ} (r : Γ →* GL (Fin a) E) (K : IntermediateField F E)
    (h : ∀ g i j, (r g : Matrix (Fin a) (Fin a) E) i j ∈ K) :
    ∃ r₁ : Γ →* GL (Fin a) ↥K, ∀ g i j,
      ((r₁ g : Matrix (Fin a) (Fin a) ↥K) i j : E) = (r g : Matrix (Fin a) (Fin a) E) i j := by
  let m : Γ →* Matrix (Fin a) (Fin a) ↥K :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, h g i j⟩
      map_one' := by
        ext i j
        simp only [Matrix.of_apply, map_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply] }
  exact ⟨m.toHomUnits, fun g i j => rfl⟩

theorem exists_continuous_model :
    ∀ (D : D7) (l : ℕ) [Fact l.Prime] (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → ∀ L₀ : FinExt l, ∃ (LL' : FinExt l) (_ : L₀.1 ≤ LL'.1) (ρ₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1), Continuous (fun g => ((ρ₁ g : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1)) ∧ mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ₁ = ρ := by
  intro D l _ a ρ hρ L₀
  obtain ⟨L, hL, h⟩ := exists_finExt_entries_mem l (G D.host.E D.nd.Om) a ρ hρ L₀
  obtain ⟨ρ₁, h₁⟩ := exists_hom_of_entries_mem ρ L.1 h
  refine ⟨L, hL, ρ₁, ?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    refine continuous_induced_rng.2 ?_
    exact (hρ.matrix_elem i j).congr fun g => (h₁ g i j).symm
  · refine MonoidHom.ext fun g => Units.ext ?_
    ext i j
    exact h₁ g i j

end GlobalTheory.CompactRepField
end

