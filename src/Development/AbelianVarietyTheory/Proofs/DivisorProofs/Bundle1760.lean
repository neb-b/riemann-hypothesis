module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumCMPreservesSchwartzHeisenber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0819
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafTW1OfAllConjugatesGood
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumCMPreservesSchwartzHeisenberStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedWeilDatum_CM_preserves_schwartz_heisenberg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) ∧
              ∀ p w, ∀ φ ∈ schA F κ, om p (co.rho B.ψ w φ) = co.rho B.ψ (actAB (cA σ) p w) (om p φ) := by
  first | exact @GlobalTheory.TransportHeisF.pres_impl | exact GlobalTheory.TransportHeisF.pres_impl | (intros; apply GlobalTheory.TransportHeisF.pres_impl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumKeepsAdmissibleForms
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilAdm

set_option maxHeartbeats 1000000 in
theorem weilAdmissible_of_heisenberg_unitary (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (κ : Type) [Fintype κ]
    (B : ((κ → AF D.host.F) × (κ → AF D.host.F)) ≃ₗ[AF D.host.F] ((κ → AF D.host.F) × (κ → AF D.host.F)))
    (O : Module.End ℂ ((κ → AF D.host.F) → ℂ))
    (hpres : ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, O φ ∈ GlobalTheory.WeilM.schA D.host.F κ)
    (himpl : ∀ w, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, O (GlobalTheory.WeilM.schr ψ w φ) = GlobalTheory.WeilM.schr ψ (B w) (O φ))
    (hunit : ∀ μ : @Measure (κ → AF D.host.F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∫⁻ x, ‖O φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) :
    ∀ l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ, l ∘ₗ O ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ := by
  intro l hl g hg
  obtain ⟨M, hMo, hM⟩ := _root_.GlobalTheory.WeilAdm.pureA_fixed_fin D.host.F ψ hψ.1.1 κ g hg
  obtain ⟨M', hM'o, hM'⟩ := _root_.GlobalTheory.WeilAdm.fintrans D.host.F κ B M hMo
  obtain ⟨U, K, hUo, hUc, hK, hfix⟩ := _root_.GlobalTheory.WeilAdm.fixed_invariant_compactSupport D ψ hψ κ M' hM'o
  obtain ⟨R, hRsb, hdec⟩ := _root_.GlobalTheory.WeilAdm.eq_sum_pureA_coset_indicator D.host.F κ U K hUo hUc hK
  obtain ⟨L, hL⟩ := _root_.GlobalTheory.WeilAdm.infLin_main D.host.F κ B
  obtain ⟨μ, hμ, C, c, hC, hc0, hcT, hpure, hslice⟩ := _root_.GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds D.host.F κ g hg U hUo
  have hpA : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ,
      GlobalTheory.WeilM.pureA D.host.F f g ∈ GlobalTheory.WeilM.schA D.host.F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hfixed : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ, ∀ m ∈ M',
      GlobalTheory.WeilM.schr ψ (finE2 D.host.F m) (O (GlobalTheory.WeilM.pureA D.host.F f g)) = O (GlobalTheory.WeilM.pureA D.host.F f g) := by
    intro f m hm
    obtain ⟨m0, hm0, hB⟩ := hM' m hm
    rw [← hB, ← himpl _ _ (hpA f), hM m0 hm0]
  have hs : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ) (r : κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ, ∀ z,
        s z = slice D.host.F (O (GlobalTheory.WeilM.pureA D.host.F f g)) r z :=
    fun f r => exists_schwartz_slice _ (hpres _ (hpA f)) r
  choose sl hsl using hs
  let A : (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
      (SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ →ₗ[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ) :=
    fun r =>
    { toFun := fun f => sl f r
      map_add' := fun f f' => by
        ext z
        rw [SchwartzMap.add_apply, hsl, hsl, hsl, show ⇑(f + f') = ⇑f + ⇑f' from funext fun _ => rfl, pureA_add, map_add (f := _)]
        rfl
      map_smul' := fun a f => by
        ext z
        rw [SchwartzMap.smul_apply, hsl, hsl, show ⇑(a • f) = a • ⇑f from funext fun _ => rfl, pureA_smul, map_smul]
        rfl }
  have hA : ∀ r f, ⇑(A r f) = slice D.host.F (O (GlobalTheory.WeilM.pureA D.host.F f g)) r := fun r f => funext (hsl f r)
  have hcont : ∀ r, Continuous (A r) := by
    intro r
    refine _root_.GlobalTheory.WeilAdm.realcont D ψ hψ κ L (A r) (C / c) (ENNReal.div_ne_top hC hc0) (fun f => ?_) (fun v f f' hf => ?_)
    · have h1 := hslice _ (hpres _ (hpA f)) (hfix _ (hfixed f)).1 r
      rw [hunit μ hμ _ (hpA f)] at h1
      have h2 := h1.trans (hpure f)
      rw [hA, ← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hcT), mul_comm]
      exact h2
    · rw [hA, hA, hf, pureA_schrInf, himpl _ _ (hpA f), hL, slice_schr]
  have hT : ∀ r ∈ R, ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ,
      l (GlobalTheory.WeilM.pureA D.host.F f (Set.indicator {y | y - r ∈ U} fun _ => (1 : ℂ))) = T f :=
    fun r hr => hl _ (hRsb r hr)
  choose T hT using hT
  refine ⟨∑ r ∈ R.attach, (T r.1 r.2).comp ⟨A r.1, hcont r.1⟩, fun f => ?_⟩
  have hΦ := hdec (O (GlobalTheory.WeilM.pureA D.host.F f g)) (hfix _ (hfixed f)).1 (hfix _ (hfixed f)).2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.comp_apply, hΦ, map_sum, ContinuousLinearMap.sum_apply, ← Finset.sum_attach R]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← hA, hT r.1 r.2]
  rfl

end GlobalTheory.WeilAdm

namespace GlobalTheory.WeilAdm

theorem transport_adm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       ∀ p, ∀ l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ, l ∘ₗ om p ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ := by
  intro D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hJA hJB κ _ co hco ω hω om htr p l hl
  have hP := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hJA hJB κ co hco ω hω om htr
  have hU := _root_.GlobalTheory.WeilUnitaryTransport.isUnitaryOn_transport D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hJA hJB κ co hco ω hω om htr
  refine weilAdmissible_of_heisenberg_unitary D ψ hψ κ (co.e.symm.trans ((actLin _ p).trans co.e)) (om p) (hP.1 p)
    (fun w φ hφ => ?_) (fun μ hμ φ hφ => hU μ hμ p φ hφ) l hl
  have h := hP.2 p (co.e.symm w) φ hφ
  simp only [GlobalTheory.WeilM.Darboux.rho, LinearEquiv.apply_symm_apply] at h
  exact h

end GlobalTheory.WeilAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLatticeInvariantSchwartzLocalStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_lattice_invariant_schwartz_local : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (w : Pl (F := F)) (g : (Fin a' × Fin (a + a') → Fv F w) → ℂ), g ∈ SB (Fin a' × Fin (a + a') → Fv F w) →
    (∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
      Acts (evFin F w) (G.M'.co.rho B.ψ γ) g (c • g)) →
    ∃ r : ℂ, g = r • G.M'.vac w := by
  first | exact @GlobalTheory.VacLine.eigen_line | exact GlobalTheory.VacLine.eigen_line | (intros; apply GlobalTheory.VacLine.eigen_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncationSpecialUnitaryMemClosureStrongApprox
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.SUAssemble


open GlobalTheory.SUAssemble in
theorem assemble : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0)) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ γ ∈ SURat σ J, ∀ x : HA (AF F) σ J, (∀ i j, ((HA.mat (AF F) σ J x).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j + algebraMap (AF F) (AF F ⊗[F] E) η * (((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j) → x ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro H1 H2 F E _ _ _ _ _ σ hcm M J hM hJ S₁ S₂ ε hε hnc T₁ T₂ η hη γ hγ x hx
  obtain ⟨S₁', S₂', ε', hs1, hs2, hne, hε', hz⟩ := H2 F E σ hcm M J hM hJ S₁ S₂ ε hε hnc
  have hηη : η * η = η := idem_sq hη
  have hεε : ε * ε' = ε' := idem_mul_of_sub hε hε' hs1 hs2
  set S := {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} with hS
  have hdiv := GlobalTheory.SUSuppSub.closure_div_mem F E σ hcm M J hJ S₁ S₂ ε hε
  have h1 : (1 : HA (AF F) σ J) ∈ closure S := subset_closure ⟨1, (SURat σ J).one_mem, 1,
    (GlobalTheory.SUSuppSub.mem_SUSupp_iff σ J).2 ⟨(SUAdelic σ J).one_mem, by
      rw [GlobalTheory.SUSuppSub.mv_one, sub_self, smul_zero]⟩, by simp⟩
  let Cg : Subgroup (HA (AF F) σ J) := Subgroup.ofDiv (closure S) ⟨1, h1⟩ hdiv
  have hmono : closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε', x = γ * h} ⊆ closure S :=
    closure_mono (by
      rintro _ ⟨g, hg, h, hh, rfl⟩
      exact ⟨g, hg, h, SUSupp_mono σ J hεε hh, rfl⟩)
  let K := Cg.comap (trunc σ J η hηη)
  have hlist : ∀ l : List ((Fin M → E) × (Fin M → E) × E),
      (∀ p ∈ l, hE σ J p.1 p.1 ≠ 0 ∧ hE σ J p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * σ p.2.2 = 1) →
      ∃ p ∈ K, (p.1 : Matrix (Fin M) (Fin M) E) =
        (l.map fun p => qr σ J p.1 p.2.2 * qr σ J p.2.1 (σ p.2.2)).prod := by
    intro l
    induction l with
    | nil =>
      intro _
      exact ⟨1, K.one_mem, by simp⟩
    | cons q l ih =>
      intro hl
      obtain ⟨p₂, hp₂, e₂⟩ := ih (fun p hp => hl p (List.mem_cons_of_mem _ hp))
      obtain ⟨hx, hy, hu⟩ := hl q List.mem_cons_self
      obtain ⟨z, hzz, c1, c2⟩ := hz q.1 q.2.1 hx hy
      obtain ⟨p₁, e₁, hp₁⟩ := _root_.GlobalTheory.SUPair.trunc_pair_mem H1 F E σ hcm M J hJ S₁' S₂' ε' hε' hne η hηη q.1 q.2.1 z q.2.2 hu hx hy
        hzz c1 c2
      refine ⟨p₁ * p₂, K.mul_mem (hmono hp₁) hp₂, ?_⟩
      rw [List.map_cons, List.prod_cons, ← e₁, ← e₂]
      rfl
  obtain ⟨hγa, hγr⟩ := hγ
  change HA.mat (AF F) σ J γ ∈ (Formalism.UG.UJ (σ : E →+* E) J).map (Formalism.UG.bc (inclR (AF F))) at hγr
  obtain ⟨g0, hg0, hg0e⟩ := Subgroup.mem_map.1 hγr
  have hmat : ((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      RingHom.mapMatrix (inclR (AF F)) (g0 : Matrix (Fin M) (Fin M) E) := by
    rw [← hg0e]
    rfl
  have hdet : (g0 : Matrix (Fin M) (Fin M) E).det = 1 := by
    have h := StrongApprox.mem_SUAdelic.1 hγa
    rw [hmat, ← RingHom.map_det] at h
    haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
    have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
      Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective
    exact hinj (h.trans (map_one _).symm)
  obtain ⟨l, hl, hle⟩ := _root_.GlobalTheory.SUGenPairs.eq_prod_pairs F E σ hcm M J hJ g0 hg0 hdet
  obtain ⟨p, hp, hpe⟩ := hlist l hl
  have hpg : p = ⟨g0, hg0⟩ := Subtype.ext (Units.ext (hpe.trans hle.symm))
  have hxe : x = trunc σ J η hηη ⟨g0, hg0⟩ := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    refine (hx i j).trans ?_
    change _ = (1 + algebraMap (AF F) (AF F ⊗[F] E) η • (rmat (F := F) g0 - 1)) i j
    rw [hmat]
    simp [rmat]
  rw [hxe, ← hpg]
  exact hp

end GlobalTheory.SUAssemble

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TupleReadBaseTupleEqFamily
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn.TwistBoundAtPlace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem tupleRead_baseTuple_eq_family : p.tupT D.what₂.mu0 = p.P.A3.A.μ0 :=
  p.charW.base.lev.xi_inj (by rw [p.tupXi D.what₂.mu0 (Or.inl rfl), p.Tp.trueColumnChoices_heckeChar_reference_eq_one, p.charW.base.lev.xi_base])

theorem twistedAt_of_mem {v : HeightOneSpectrum (𝓞 D.what₂.LL)} (hv : v ∈ p.R.twPl) : TwistedAt D (D.plEq.symm v) := by
  intro he
  apply p.charW.tup.mu_ne v hv
  have := p.tupAt (D.plEq.symm v)
  rw [he, tupleRead_baseTuple_eq_family, Equiv.apply_symm_apply] at this
  exact this.symm

theorem conj_mem {v : HeightOneSpectrum (𝓞 D.what₂.LL)} (hv : v ∈ p.R.twPl) : Formalism.DivisionValues.conjPl v ∈ p.R.twPl := by
  by_contra h
  have := p.charW.tup.mu_off _ h
  rw [p.charW.tup.mu_conj] at this
  exact p.charW.tup.mu_ne v hv this

end Point


set_option maxHeartbeats 1600000 in
theorem hasTwistBound_at {eps : ℝ} {Fm : FamP eps} {x : ℝ} {hx : Fm.x1 < x} {i : Fm.Ix x} (p : Pt Fm x hx i)
    {r : TwoRuns p.T p.P.Gp} {c : OnConst} {O : Obj p c} (hR : RecAt p (Fm.parT x hx i) r O)
    (hE : ∀ v ∈ p.R.twPl, ∀ j, GlobalTheory.TwistIndex.ExportTie p.P.A3.A (Fm.ex x hx i).nch (twE Fm x hx i) (R2 p) j (F2 p).P0
      (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v))
    (hS : LeafSup O) (hK : GlobalTheory.TraceClassRank.RankAtPlaces O)
    {N0 : (Fm.D x i).ntw.Tw → ℕ} {S : ∀ (i' : (Fm.D x i).ntw.Tw) (j : ℕ) (b : Bool), Finset ((Fm.D x i).nexp.Dat i' j b)}
    (hG : Formalism.MainNotions.TwGoodAt (Fm.D x i) (Fm.ex x hx i).nch ⟨twE Fm x hx i, N0, S⟩) : HasTwistBound O := by
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hR.1.tied
  have tied : ∀ v ∈ p.R.twPl, TwistedAt (Fm.D x i) ((Fm.D x i).plEq.symm v) ∧
      ∀ j, GlobalTheory.TwistIndex.TiedAt p.P.A3.A (Fm.ex x hx i).nch (twE Fm x hx i) O v j (id j) := fun v hv =>
    ⟨twistedAt_of_mem p hv, fun j => ⟨(r.used v).full, p.alg, R2 p, p.κ, p.v₀, (hR.1.ok.laws v).p, fw2 p, hinj,
      (Fm.ex x hx i).errX, ownAt (Fm.D x i) v, _, _, _, z j, act j, GlobalTheory.OntoChain.mirIncl (R2 p), r.lev j, (F2 p).P0, (F2 p).ψ0⁻¹, 1, y v j,
      (ht v j).1, hE v hv j⟩⟩
  exact GlobalTheory.TwistIndex.exists_leafTW1_of_twGoodAt p.P.A3.A (Fm.ex x hx i).nch ⟨twE Fm x hx i, N0, S⟩ hG O id
    Function.injective_id (GlobalTheory.TwistIndex.goodPartLattice_of_leafSup hS)
    (fun w hw => ⟨fun j => ((hK w hw).1 j).2.1, fun j => ((hK w hw).2 j).2.1⟩)
    (fun w hw => ⟨tied w hw, tied _ (conj_mem p hw)⟩)

end GlobalTheory.BigOn.TwistBoundAtPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceStepFactorInverseAwayUnit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.SqTwist

theorem twist_factor : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs → ∀ (v : Bs.P), v.1 ∈ (GlobalTheory.SqStep.chs G i j t).T →
    v.1 ∉ G.pl.S0 → ∀ (s : ℤˣ) (z : ℤ), ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) ≠ 0 → ∃ b : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) b ∧
      D.what₂.embLL b * ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) = 1 := by
  intro D T Lc sc G μ₀ hL W S hN i j t Bs hB v hvT hvS s z hf
  classical
  set τ := Bs.τ v with hτ
  set w := GlobalTheory.AdelicU.splitPrime τ with hw
  have hunder : w.under (𝓞 D.host.F) = v.1 := GlobalTheory.AdelicU.splitPrime_under τ
  have hloc : w ∈ locPl G t := hB.2.2.2 v hvT
  have hW0 : w ∉ G.pl.W0 := by
    intro h
    obtain ⟨u, hu, hu'⟩ := Finset.mem_image.1 h
    apply hvS
    have := G.pl.under_w hu
    rw [hu'] at this
    rw [← hunder, this]
    exact hu
  have htw : w ∈ twPl G t := Finset.mem_filter.2 ⟨hloc, hW0⟩
  have hQ : w ∈ Lc.Q t := by
    rcases Finset.mem_union.1 hloc with h | h
    · exact absurd h hW0
    · exact h
  have hq : Ideal.absNorm w.asIdeal = Ideal.absNorm v.1.asIdeal := GlobalTheory.LFun.SplitChart.absNorm_splitPrime τ
  have hQn : 0 < Qn G t := by
    unfold Qn
    refine Finset.prod_pos fun u _ => Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact u.ne_bot
  have hqd : Ideal.absNorm v.1.asIdeal ∣ Qn G t := hq ▸ Finset.dvd_prod_of_mem _ htw
  obtain ⟨hmu, hchi⟩ := _root_.GlobalTheory.TwistUnr.mu0_chiH_unrAt G hL i j t w hQ (by rw [hunder]; exact hvS)
  have hc := _root_.GlobalTheory.TwistCond.condExp_twist_eq_one G hL i j t τ hmu hchi hQ
  obtain ⟨g, hg, hgd⟩ := _root_.GlobalTheory.TwistGaussInt.gauss_dvd G W S hL hN i j t τ Bs.ψ (hB.2.2.1 v.1 v.2) hloc hc
  obtain ⟨x, hx, hxa⟩ := _root_.GlobalTheory.TwistStepVal.step_val G W S hL hN i j t τ hmu hchi htw
  set ν := chrW (GlobalTheory.SqStep.chs G i j t).ν τ with hν
  set s' : (Fv D.host.F v.1)ˣ := Units.map (Int.castRingHom _).toMonoidHom s with hs'

  have hs2 : s' ^ 2 = 1 := by
    rw [hs', ← map_pow, Int.units_sq, map_one]
  have hsgn : ((ν s' : ℂˣ) : ℂ) = 1 ∨ ((ν s' : ℂˣ) : ℂ) = -1 := by
    have h2 : ((ν s' : ℂˣ) : ℂ) * ((ν s' : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul, ← sq, hs2, map_one, Units.val_one]
    exact mul_self_eq_one_iff.1 h2
  obtain ⟨e, he, hea⟩ : ∃ e : D.what₂.LL, D.what₂.embLL e = ((ν s' : ℂˣ) : ℂ) ∧ GlobalTheory.Square.IsAwayUnit (Qn G t) e := by
    rcases hsgn with h | h
    · exact ⟨1, by rw [map_one, h], GlobalTheory.Square.AwayClosure.of_pow_eq_one _ one_pos (one_pow 1)⟩
    · exact ⟨-1, by rw [map_neg, map_one, h], GlobalTheory.Square.AwayClosure.of_pow_eq_one _ two_pos (by norm_num)⟩

  set q : ℕ := Ideal.absNorm v.1.asIdeal with hqdef
  have hqa : GlobalTheory.Square.IsAwayUnit (Qn G t) ((q : D.what₂.LL) ^ (-z)) := by
    have hn : ∀ n : ℕ, GlobalTheory.Square.IsAwayUnit (Qn G t) ((q : D.what₂.LL) ^ n) := by
      intro n
      have h1 : (((q : 𝓞 D.what₂.LL) ^ n : 𝓞 D.what₂.LL) : D.what₂.LL) = (q : D.what₂.LL) ^ n := by
        simp only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_natCast]
      rw [← h1]
      apply GlobalTheory.Square.AwayClosure.of_dvd (k := n)
      exact pow_dvd_pow_of_dvd (Nat.cast_dvd_cast hqd) n
    rcases Int.eq_nat_or_neg (-z) with ⟨n, hn' | hn'⟩
    · rw [hn', zpow_natCast]; exact hn n
    · rw [hn', zpow_neg, zpow_natCast]; exact GlobalTheory.Square.AwayClosure.inv hQn (hn n)
  have hga : GlobalTheory.Square.IsAwayUnit (Qn G t) (g : D.what₂.LL) :=
    GlobalTheory.Square.AwayClosure.of_dvd (k := 1) (by rw [pow_one]; exact hgd.trans (Nat.cast_dvd_cast hqd))
  set a : D.what₂.LL := e * ((q : D.what₂.LL) ^ (-z) * (g : D.what₂.LL) * x) with ha
  have haA : GlobalTheory.Square.IsAwayUnit (Qn G t) a :=
    GlobalTheory.Square.AwayClosure.mul hea (GlobalTheory.Square.AwayClosure.mul (GlobalTheory.Square.AwayClosure.mul hqa hga) hxa)
  have hfa : D.what₂.embLL a = ((ν s' : ℂˣ) : ℂ) * eps Bs.ψ ν z := by
    rw [ha]
    unfold eps
    rw [hc]
    simp only [map_mul, map_zpow₀, map_natCast, he, hg, hx, Nat.cast_one, pow_one]
    congr 1
    rw [neg_one_mul]
  refine ⟨a⁻¹, GlobalTheory.Square.AwayClosure.inv hQn haA, ?_⟩
  rw [map_inv₀, ← hfa]
  rw [← hfa] at hf
  exact inv_mul_cancel₀ hf

end GlobalTheory.SqTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTransportCmExtensionIsUnitaryOn
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.WeilAdmCMUnit

theorem isUnitaryOn_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om :=
  _root_.GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF

end GlobalTheory.WeilAdmCMUnit
end

