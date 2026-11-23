module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0538
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0297
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0397
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0490
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0330

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtraColumnRangeMembership
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopStep

open GlobalTheory.Fam.Inhab GlobalTheory.Fam.FamInhab

section
variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (P : LevelP R.Pg D.R.r ℂ)

theorem lift_lev_pt (hl : R.toLevCh.Is A.μ0) (hθ : IsInfFam R.θ) (t : T) (k : ℕ) (hk : k < D.R.m) {V : HSp D} (hV : V.SigOK)
    (hr : V.rank = D.R.r + (k + 1) * D.R.t) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (Lev.EAf D)} {N : ℕ} (hβ : IsSDFrame V β Λ N)
    {om : Om (Yc D k) V} (hom : IsWeilDatumO R.ψ (Yc D k) V (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 om) {f₀ f f' : WO (Yc D k) V → ℂ}
    (hf : IsStepVecOf R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (R.ΛY k) Λ (R.βY k) β (R.datYt t k R.triv) (R.chi (k + 1))
      (R.Q t) (R.xiR t) f₀ f)
    (hf' : IsStepVecOf R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (R.ΛY k) Λ (R.βY k) β (R.datYt t k P) (R.chi (k + 1))
      (R.Q t) (R.xiR t) f₀ f') (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) (F : GA D V → ℂ) (φ : PolF D V.rank (Yc D k).rank)
    (hi : ∀ g, IntegrableOn (fun h => thetaKO om g h
      (pureTensorO R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (onb (R.MY k)) (onb M) f φ) * F h) 𝓕 ν)
    (U : GA D (Yc D k) → ℂ)
    (hU : ∀ κ ∈ levS (Yc D k) (R.βY k) (R.datYt t k P), ∀ g, U (g * κ) = levChi (Yc D k) (R.βY k) (R.datYt t k P) κ * U g)
    (he : ∀ g, Lift.liftInt ν 𝓕 (thetaKO om)
      (pureTensorO R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (onb (R.MY k)) (onb M) f φ) F g = U g) :
    liftS om ν 𝓕 F (pureTensorO R.ψ R.θ (Yc D k) V (cart (R.MY k)) (cart M) (onb (R.MY k)) (onb M) f' φ) =
      (Nat.card P.H : ℂ) • U := by
  haveI := finite_H P
  haveI : Fintype P.H := Fintype.ofFinite _
  choose κ hκ using fun p : P.H => GlobalTheory.ChainEquiv.lifts_chain R.toLevCh _ hl t k hk p.1
  obtain ⟨⟨a1, a2, a3⟩, b1, b2, b3⟩ := GlobalTheory.StepVecLaw.levRes_chrStep hl t ⟨k, hk⟩
  have s1 := sd (hl.βY k hk)
  have s2 := sd hβ
  have hs := @GlobalTheory.StepVecSum.stepVec_eq_sum D R.ψ R.θ (Yc D k) V _ _ om _ _ _ _ _ _ f₀ f f' hom (D.sp.Y_sig _) hV
    (GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MY k)) (GlobalTheory.Chain.VacVec.cart_isCartanInv M) s1.1 s2.1 s1.2 s2.2 D.R.r D.R.t k (r_le_Y k)
    (rankY hk.le) hr R.Pg (R.Q t) (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).2 R.chi (R.xiR t) P _ hf hf'
    (fun PP hP => ⟨a1 PP hP, b1 PP hP⟩) (fun PP hP => ⟨a2 PP hP, b2 PP hP⟩) a3 b3 κ hκ
  have hth : IsThetaFunO R.ψ (Yc D k) V f := (GlobalTheory.Chain.StepVac.stepVec_vac s1.1 s2.1 (by
    rw [rankY hk.le, hr]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _) hf).1
  exact (lift_sum hom hθ _ _ _ _ hth κ (fun p => (hκ p).1) _ (fun p => levChi_ne_zero _ _) hs ν 𝓕 F φ hi U he
    fun p g => hU _ (levChi_lift (L := R.datYt t k R.triv) P p (hκ p)) g).2

theorem lift_ioX_pt (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) (t : T) (j : ℕ)
    (h : j + 2 * 0 + 2 = D.R.m) (F : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e))
    (hF : ∀ κ ∈ levS (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P), ∀ φ x g,
      (R.ioX t F).1 (R.ItX φ x) (g * κ) = levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P) κ *
        (R.ioX t F).1 (R.ItX φ x) g)
    {v : WO (Yc D (j + 1)) D.sp.X' → ℂ}
    (hv : IsStepVecOf R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX) (R.ΛY (j + 1)) R.ΛX (R.βY (j + 1)) R.βX
      (R.datYt t (j + 1) P) (R.chi D.R.m) (R.Q t) (R.xiR t) (vacT R j h) v) (Q x) :
    liftS (omT R t j h) (R.νX t) (R.fdX t) (F.1 x) (pureTensorO R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX)
      (onb (R.MY (j + 1))) (onb R.MX) v Q) = (Nat.card P.H : ℂ) • (ioXT R t j h F).1 (itXT R j h Q x) := by
  have e : R.chi D.R.m = R.chi (j + 1 + 1) := congrArg R.chi (show j + 1 + 1 = D.R.m from h).symm
  have h1 := top_vec hc t j h
  rw [e] at h1 hv
  have key : ∀ n (e : D.R.m - 1 = n), ∀ κ ∈ levS (Yc D n) (R.βY n) (R.datYt t n P), ∀ φ x g,
      ((Eq.rec (motive := fun n _ => LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n)
        (R.ioX t) e : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n) F).1
        ((Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) R.ItX e :
          PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) φ x) (g * κ) =
      levChi (Yc D n) (R.βY n) (R.datYt t n P) κ *
        ((Eq.rec (motive := fun n _ => LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n)
        (R.ioX t) e : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n) F).1
        ((Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) R.ItX e :
          PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) φ x) g := by
    intro n e; subst e; exact hF
  exact lift_lev_pt P hl hm.inf t (j + 1) (by omega) D.sp.X'_sig (rank_top h) R.MX hl.βX (top_weil hc t j h) h1 hv
    _ _ _ Q ((top_io hc t j h).integ F Q x) _ (fun κ hκ g => key _ (idx_top h) κ hκ Q x g) ((top_io hc t j h).eq F Q x)

end

end GlobalTheory.TopStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorConjugateHalfVacuumEqSemichara
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjHalfHeis

theorem mem_localization_of_mem_halfBO {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (c : ℕ)
    (y : Formalism.L2.Col.HomE E a b) (hy : y ∈ halfBO SS M c) (Q : HeightOneSpectrum (𝓞 E))
    (hQ : ¬ (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS)) : y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  have h1 := (Formalism.L2.Ker.mem_twO M c _ y).1 hy Q
  have h0 : expS SS Q = 0 := by
    unfold expS
    rw [if_neg (fun h => hQ (Or.inl h)), if_neg (fun h => hQ (Or.inr h))]
  rw [h0, zpow_zero, inv_one, one_smul] at h1
  exact h1


set_option maxHeartbeats 400000 in
theorem off_part_mem (D : D7) (S T : HSp D) (Λ : AddSubgroup (WO S T))
    (hstab : ∀ w : AE D, finPart D w ∈ intAE D → ∀ u ∈ Λ, w • u ∈ Λ)
    (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) (he : IsIdemSum e SS) (c : ℕ) (hc : 0 < c) (d : 𝓞 D.host.E) (hd0 : d ≠ 0)
    (hdP : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (c : 𝓞 D.host.E) ∈ Q.asIdeal → d ∈ Q.asIdeal →
      Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS)
    (Y : WO S T) (hcY : incA D (c : D.host.E) • Y ∈ Λ) (hdY : incA D (d : D.host.E) • Y ∈ Λ) :
    (1 - e - cA D e) • Y ∈ Λ := by
  obtain ⟨a₁, a₂, ha₁, ha₂, hsum⟩ := GlobalTheory.OffIdemTwo.off_two D e SS he c hc d hd0 hdP
  have h : (1 - e - cA D e) • Y = a₁ • (incA D (c : D.host.E) • Y) + a₂ • (incA D (d : D.host.E) • Y) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    rw [hsum]; ring
  rw [h]
  exact add_mem (hstab _ ha₁ _ hcY) (hstab _ ha₂ _ hdY)


open GlobalTheory.LatVac in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem heisO_conjHalf_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ f₀, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') f₀ → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, heisO ψ S T (((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => cA D e * incA D r) f₀ = alV D.host.d sc (embH (tauE D) δ y') • heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm))) f₀ := by
  intro D ψ θ S T a b hS hT δ sc hP e SS he N N' c hc hcP h2qd hLa ΛS ΛT hSd hTd hΛS hΛT f₀ hf₀ y' hy'
  set M : Matrix (Fin T.rank) (Fin S.rank) D.host.E :=
    (LinearMap.toMatrix' y').reindex (finCongr hT.symm) (finCongr hS.symm) with hM
  set Y := GlobalTheory.VacUnique.finRat S T M with hY
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  have hvac : IsLatVac (heisO ψ S T) Λ f₀ := by
    have h := hf₀.2.lat
    rw [hΛ, hΛS, hΛT]; exact h
  have hstab : ∀ w : AE D, finPart D w ∈ intAE D → ∀ u ∈ Λ, w • u ∈ Λ :=
    fun w hw u hu => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ w hw u hu
  have hsmM : ∀ (r : D.host.E) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E),
      GlobalTheory.VacUnique.finRat S T (r • X) = incA D r • GlobalTheory.VacUnique.finRat S T X := by
    intro r X
    ext i j
    change (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (r * X i j) = incA D r * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] X i j)
    rw [show incA D r = (1 : AF D.host.F) ⊗ₜ[D.host.F] r from rfl, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hsm : ∀ (r : D.host.E) (x : Formalism.L2.Col.HomE D.host.E a b),
      GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (r • x)).reindex (finCongr hT.symm) (finCongr hS.symm)) =
        incA D r • GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' x).reindex (finCongr hT.symm) (finCongr hS.symm)) := by
    intro r x
    ext i j
    change (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (LinearMap.toMatrix' (r • x) _ _) =
      incA D r * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] (LinearMap.toMatrix' x _ _))
    rw [LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
      show incA D r = (1 : AF D.host.F) ⊗ₜ[D.host.F] r from rfl, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hsmY : ∀ r : D.host.E, GlobalTheory.VacUnique.finRat S T
      ((LinearMap.toMatrix' (r • y')).reindex (finCongr hT.symm) (finCongr hS.symm)) = incA D r • Y := fun r => by
    rw [hsm]
  have hrat := fun x hx => GlobalTheory.AdForm.RatLatPer.finRat_mem_latO_of_perO D ψ θ S T a b hS hT δ sc hP N N' ΛS ΛT hSd hTd hΛS hΛT x hx
  have hc0 : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hnat : ∀ (n : ℕ) (u : WO S T), n • u = incA D (n : D.host.E) • u := by
    intro n u; rw [map_natCast, Nat.cast_smul_eq_nsmul]

  have ha : c • Y ∈ Λ := by
    rw [hnat, ← hsmY]; exact hrat _ (GlobalTheory.HalfBCMul.cmul_mem_perO_of_mem_halfBO D a b N N' SS c hc y' hy')

  obtain ⟨t, ht0, htP, htm⟩ := GlobalTheory.HalfTmul.exists_tmul_mem_perO D a b N N' SS c hc y' hy'
  have heI : finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D := GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e SS he t htP
  set Z := (e * incA D ((t : D.host.E))⁻¹) • GlobalTheory.VacUnique.finRat S T
    ((LinearMap.toMatrix' (((t : D.host.E) * (c : D.host.E)⁻¹) • y')).reindex (finCongr hT.symm) (finCongr hS.symm)) with hZ
  have hZm : Z ∈ Λ := hstab _ heI _ (hrat _ htm)
  have he2 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have ht0' : (t : D.host.E) ≠ 0 := by
    intro h; exact ht0 (by exact_mod_cast h)
  have hb : e • Y = c • (e • Z) := by
    have h1 : (c : D.host.E) * ((t : D.host.E)⁻¹ * ((t : D.host.E) * (c : D.host.E)⁻¹)) = 1 := by
      field_simp
    have h2 : incA D (c : D.host.E) * (e * (e * incA D (t : D.host.E)⁻¹) * incA D ((t : D.host.E) * (c : D.host.E)⁻¹)) = e := by
      calc _ = (e * e) * incA D ((c : D.host.E) * ((t : D.host.E)⁻¹ * ((t : D.host.E) * (c : D.host.E)⁻¹))) := by
              simp only [map_mul]; ring
        _ = e := by rw [h1, map_one, mul_one, he2]
    rw [hZ, hsmY]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
    rw [← map_natCast (incA D) c]
    calc e * Y i j = (incA D (c : D.host.E) * (e * (e * incA D (t : D.host.E)⁻¹) *
          incA D ((t : D.host.E) * (c : D.host.E)⁻¹))) * Y i j := by rw [h2]
      _ = _ := by ring

  have hR0 : (1 - e - cA D e) • Y ∈ Λ := by
    obtain ⟨d, hd0, hdm, hdP⟩ := GlobalTheory.OffDen.exists_den_avoid D.host.E a b (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')
      (fun Q => Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) c hc y' (GlobalTheory.HalfBCMul.cmul_mem_perO_of_mem_halfBO D a b N N' SS c hc y' hy') (mem_localization_of_mem_halfBO SS _ c y' hy')
    have hdY : incA D (d : D.host.E) • Y ∈ Λ := by
      rw [← hsmY]; exact hrat _ hdm
    exact off_part_mem D S T Λ hstab e SS he c hc d hd0 hdP Y (hnat c Y ▸ ha) hdY
  have heint : finPart D e ∈ intAE D := by
    have h := GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e SS he 1 (fun Q _ h => Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h))
    simpa using h
  set R := (1 - cA D e) • Y with hRdef
  have hR : R ∈ Λ := by
    have h : R = c • (e • Z) + (1 - e - cA D e) • Y := by
      rw [hRdef, ← hb, ← add_smul]; congr 1; ring
    rw [h]; exact add_mem (nsmul_mem (hstab _ heint _ hZm) c) hR0
  have h2 : ∀ Q ∈ SS, (2 : 𝓞 D.host.E) ∉ Q.asIdeal := by
    intro Q hQ h; apply h2qd Q hQ
    obtain ⟨t, ht⟩ := D.host.toHostRaw.two_dvd_condN
    have e2 : ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) = 2 * ((t : ℕ) : 𝓞 D.host.E) := by
      rw [show D.host.QS * D.host.q * D.host.d = 2 * t from ht]; push_cast; ring
    rw [e2]; exact Q.asIdeal.mul_mem_right _ h
  have hcoc : ψ (symplOH S T (cA D e • Y) R) = 1 :=
    GlobalTheory.ConjHalfCocycle.char_symplOH_conjHalf_rest D ψ S T ΛS ΛT hP.std hSd hTd e SS he h2 c hc Y Z ha hZm hb

  have hbil : ∀ (x y : WO S T) (k : ℕ), symplOH S T (k • x) (k • y) = (k * k) • symplOH S T x y := by
    intro x y k
    have h1 : symplO S T (k • x) (k • y) = (k * k) • symplO S T x y := by
      rw [← symplHom_apply, map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply, symplHom_apply, smul_smul]
    rw [symplOH, symplOH, h1]
    simp only [nsmul_eq_mul]
    ring
  have hcc : c • c • Y ∈ Λ := nsmul_mem ha c
  obtain ⟨k, hk, hsign⟩ := GlobalTheory.LatVacSign.heisO_finRat_sign ψ S T ΛS ΛT hP.std hSd hTd f₀ hvac
    (-(((c : D.host.E) ^ 2) • M)) (by
      rw [neg_neg, hsmM, ← hY, pow_two, map_mul, mul_smul, ← hnat, ← hnat]; exact hcc)
  rw [neg_neg, hsmM, ← hY, pow_two, map_mul, mul_smul, ← hnat, ← hnat] at hsign
  set X1 := cA D e • (c • c • Y) with hX1
  have hY1 : cA D e • Y + R = Y := by rw [hRdef, ← add_smul, add_sub_cancel, one_smul]
  have hdec : c • c • Y = X1 + c • c • R := by
    calc c • c • Y = c • c • (cA D e • Y + R) := by rw [hY1]
      _ = X1 + c • c • R := by rw [hX1, smul_add, smul_add, smul_comm (cA D e) c, smul_comm (cA D e) c]
  have hfixX := (GlobalTheory.IdemSumVac.heisO_idemSum_fix D ψ S T Λ f₀ hvac hstab e SS he _ hcc).2
  have hfixXn : heisO ψ S T (-X1) f₀ = f₀ := by
    have h := (GlobalTheory.IdemSumVac.heisO_idemSum_fix D ψ S T Λ f₀ hvac hstab e SS he _ (neg_mem hcc)).2
    rwa [smul_neg] at h
  have hzero : symplOH S T (-X1) X1 = 0 := by
    have h0 : hO S T (-X1) X1 = 0 := by
      rw [hX1, ← smul_neg, GlobalTheory.LatVacSign.hO_smul_smul, GlobalTheory.LatVac.cA_cA, mul_comm (cA D e) e, he.2, zero_mul]
    rw [symplOH, symplO, h0, mul_zero, map_zero, mul_zero]
  have hinv : ∀ g, heisO ψ S T (-X1) (heisO ψ S T X1 g) = g := by
    intro g
    rw [GlobalTheory.LatVac.heisO_heisO, hzero, AddChar.map_zero_eq_one, one_smul, neg_add_cancel, GlobalTheory.LatVac.heisO_zero]
  have hcoc4 : ψ (symplOH S T X1 (c • c • R)) = 1 := by
    have e1 : X1 = c • c • (cA D e • Y) := by rw [hX1, smul_comm (cA D e) c, smul_comm (cA D e) c]
    rw [e1, hbil, hbil, ← mul_nsmul, AddChar.map_nsmul_eq_pow, hcoc, one_pow]
  obtain ⟨m, hm⟩ := id hcP
  have hR2eq : c • c • R = R + 2 • ((2 * m * m + 2 * m) • R) := by
    have h1 : R + 2 • ((2 * m * m + 2 * m) • R) = (1 + 2 * (2 * m * m + 2 * m)) • R := by
      rw [add_smul 1 (2 * (2 * m * m + 2 * m)) R, one_smul, mul_smul]
    rw [h1, smul_smul]
    congr 1; subst hm; ring
  have hRR : heisO ψ S T (c • c • R) f₀ = heisO ψ S T R f₀ := by
    have hmR : (2 * m * m + 2 * m) • R ∈ Λ := nsmul_mem hR _
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ R (2 • ((2 * m * m + 2 * m) • R)) f₀
    have hs : symplOH S T R (2 • ((2 * m * m + 2 * m) • R)) = symplO S T R ((2 * m * m + 2 * m) • R) := by
      rw [symplOH, ← symplHom_apply, map_nsmul, symplHom_apply, nsmul_eq_mul, ← mul_assoc]
      have h12 : algebraMap D.host.F (AF D.host.F) (1 / 2) * ((2 : ℕ) : AF D.host.F) = 1 := by
        rw [← map_natCast (algebraMap D.host.F (AF D.host.F)), ← map_mul]; norm_num
      rw [h12, one_mul]
    rw [hvac.1 _ hmR, hs, GlobalTheory.LatVac.char_sympl_eq_one hP.std hSd hTd hR hmR, one_smul, ← hR2eq] at h1
    exact h1.symm
  have hRk : heisO ψ S T R f₀ = ((-1 : ℂ) ^ k) • f₀ := by
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ X1 (c • c • R) f₀
    rw [hcoc4, one_smul, ← hdec, hsign, hRR] at h1
    have h2' := congrArg (heisO ψ S T (-X1)) h1
    rw [hinv, GlobalTheory.LatVac.heisO_smul, hfixXn] at h2'
    exact h2'

  obtain ⟨k₀, hk₀⟩ := GlobalTheory.HalfBInt.trace_int D ψ θ S T a b hS hT δ sc hP e SS he N N' c hc hcP h2qd ΛS ΛT hSd hTd hΛS hΛT y' hy'
  have hα := GlobalTheory.SemiTrace.alV_embH_eq_neg_one_zpow D ψ θ S T a b hS hT δ sc hP y' k₀ hk₀
  have hkk : k = (c : ℤ) ^ 4 * k₀ := by
    have e1 : GlobalTheory.LatVac.hRat S T (-(((c : D.host.E) ^ 2) • M)) (-(((c : D.host.E) ^ 2) • M)) =
        ((c : ℚ) ^ 4 : ℚ) • GlobalTheory.LatVac.hRat S T M M := by
      rw [← neg_smul, GlobalTheory.LatVacSign.hRat_smul_smul, star_neg, star_pow, star_natCast, Algebra.smul_def]
      push_cast; ring
    have e2 : (k : ℚ) = (c : ℚ) ^ 4 * k₀ := by
      rw [hk, e1, mul_smul_comm, map_smul, hk₀, smul_eq_mul]
    exact_mod_cast e2
  have hodd : Odd ((c : ℤ) ^ 4) := by
    obtain ⟨m', hm'⟩ := id hcP
    exact (show Odd (c : ℤ) from ⟨m', by exact_mod_cast hm'⟩).pow
  have hsgn : ((-1 : ℂ) ^ k) = alV D.host.d sc (embH (tauE D) δ y') := by
    rw [hα, hkk, _root_.zpow_mul, hodd.neg_one_zpow]
  have hα2 : alV D.host.d sc (embH (tauE D) δ y') * alV D.host.d sc (embH (tauE D) δ y') = 1 := by
    rw [hα, ← mul_zpow]; norm_num

  have hLHS : M.map (fun r => cA D e * incA D r) = cA D e • Y := by
    have h0 : infPart D (cA D e) = 0 := GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum he)
    ext i j
    change cA D e * incA D (M i j) = cA D e * ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] M i j)
    rw [show (pairA D.host.F 0 1) ⊗ₜ[D.host.F] M i j = ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D (M i j) by
      rw [show incA D (M i j) = (1 : AF D.host.F) ⊗ₜ[D.host.F] M i j from rfl, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul], ← mul_assoc, GlobalTheory.PlaceDatum.mul_pair_one h0]
  have hfin := GlobalTheory.LatVac.heisO_heisO ψ (cA D e • Y) R f₀
  rw [hRk, hsgn, GlobalTheory.LatVac.heisO_smul, hcoc, one_smul, hY1] at hfin
  rw [hLHS, ← hfin, smul_smul, hα2, one_smul]

end GlobalTheory.ConjHalfHeis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarsOfGivenData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

namespace GlobalTheory.ChainTw

theorem scalars_of_given_all : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → GlobalTheory.Core.Rk.SW.HeckeFormNS D → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  intro hHCF hCRD hDSC hHCM hCW hHowe hUDG D G _ _ Pl0 T A Ks _ _ _ R F g hNG hHecke
  have soft : SoftQ D := _root_.GlobalTheory.ChainTw.softQ_all hHCF hCRD D
  have law : LevelLawQ D := _root_.GlobalTheory.ChainTw.TwLaw.levelLawQ D
  have restore : Restore D := _root_.GlobalTheory.ChainTw.restore_holds D
  have lfull : LFull D := _root_.GlobalTheory.ChainTw.lFull_holds D
  have upSpan : UpSpanQ D := _root_.GlobalTheory.ChainTw.UpSpanTw.upSpanQ_of hDSC hHCM hCRD hCW D law
  have upAdj : UpAdjQ D := _root_.GlobalTheory.ChainTw.upAdjQ_of_cuspRapidDecay hCRD D
  have upVal : UpVal D := _root_.GlobalTheory.ChainTw.upVal_of_span_adj D soft upSpan upAdj
  have exact : StepExactNS D :=
    _root_.GlobalTheory.ChainTw.ExactNS.stepExactNS D hHecke soft (_root_.GlobalTheory.ChainTw.Peel.qPeel_holds hUDG hCRD D) (_root_.GlobalTheory.ChainTw.LevIntProof.levInt D law)
  have lam : StepLam D := _root_.GlobalTheory.ChainTw.stepLam_of_ns D soft (_root_.GlobalTheory.ChainTw.upParQ_of_transfer hCRD hHowe D) (_root_.GlobalTheory.ChainTw.upQ_holds hCRD D)
    (_root_.GlobalTheory.LowerBlockParam.qOfVal D soft) upVal exact lfull restore
  have hX : RangeX R := _root_.GlobalTheory.ChainTw.rangeX_of_given R F g
  have chain : ∀ h : RangeX R, RChain R h := _root_.GlobalTheory.ChainTw.rChain_of_given R F g
  have zeta : RealZetaQ D := _root_.GlobalTheory.RealZetaTw.realZetaTw hHCM D (_root_.GlobalTheory.TwArch.archOnRecord_closed hDSC hHCM D)
  have unif : RUnif R hX := _root_.GlobalTheory.ChainTw.UnifFree.rUnif_of R F g hNG zeta restore hX (chain hX)
    (_root_.GlobalTheory.RealMeasOne.one_real_measure R F g chain hX) (_root_.GlobalTheory.ChainTw.VolScale.rVol_of_given R F g chain hX) (_root_.GlobalTheory.ChainTw.RNrmProof.rNrm_of_given R F g)
  exact GlobalTheory.T.chainStep_scalars_of_realisation R F g hNG soft (_root_.GlobalTheory.LowerBlockParam.qOfVal D soft) (_root_.GlobalTheory.ChainTw.lPos_of_rapidDecay hCRD D) lfull lam hX
    (chain hX) (_root_.GlobalTheory.ChainTwNorm.normX R F g hX) unif (_root_.GlobalTheory.ChainTw.rowPar_of_chain hCRD R F g chain hX) (_root_.GlobalTheory.ChainTw.IPDictPf.main R F g)

end GlobalTheory.ChainTw
end

