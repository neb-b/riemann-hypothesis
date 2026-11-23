module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangia
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1785
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0424
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContentLeDetDepthAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalGoodPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LinWAt

theorem nonempty_emb_of_splitsFully {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (hv : SplitsFully E v) :
    Nonempty (E →ₐ[F] Fv F v) := by
  set q : Ideal ℤ := v.asIdeal.under ℤ with hq
  obtain ⟨g, hg⟩ := (Submodule.IsPrincipal.principal q)
  have hqs : q = Ideal.span {((g.natAbs : ℕ) : ℤ)} := by
    rw [hg]; exact Eq.symm (Int.span_natAbs g)
  have hqne : q ≠ ⊥ := by
    intro h0
    apply v.ne_bot
    exact Ideal.eq_bot_of_comap_eq_bot h0
  have hg0 : g ≠ 0 := by rintro rfl; apply hqne; rw [hg]; simp
  have hp : (g.natAbs).Prime := by
    have hI : (Ideal.span {((g.natAbs : ℕ) : ℤ)}).IsPrime := hqs ▸ (Ideal.IsPrime.under ℤ v.asIdeal)
    have hne : ((g.natAbs : ℕ) : ℤ) ≠ 0 := by simpa using hg0
    exact Nat.prime_iff_prime_int.2 ((Ideal.span_singleton_prime hne).1 hI)
  have hmem : ((g.natAbs : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    have : ((g.natAbs : ℕ) : ℤ) ∈ q := by rw [hqs]; exact Ideal.subset_span rfl
    rw [hq, Ideal.under_def, Ideal.mem_comap] at this
    simpa using this
  have h : (Ideal.primesOver (Ideal.span {((g.natAbs : ℕ) : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
    rw [← hqs]; exact hv
  rw [GlobalTheory.AdelicU.nonempty_split_iff hcm]
  exact GlobalTheory.GoodPlace.ncard_primesOver_eq_two hcm.2.2.1 hp h v hmem

end GlobalTheory.LinWAt

namespace GlobalTheory.LinWAt

theorem locCo_form {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x u : W) :
    (GlobalTheory.LatVac.locCo co v x).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v u).2 -
      (GlobalTheory.LatVac.locCo co v u).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v x).2 = evFin F v (B x u) := by
  rw [co.form]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub]

theorem locCo_surj {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (w : (κ → Fv F v) × (κ → Fv F v)) : ∃ u : W, At (evFin F v) u ∧ GlobalTheory.LatVac.locCo co v u = w := by
  refine ⟨co.e.symm (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)), ?_, ?_⟩
  · intro a ha
    rw [← LinearEquiv.map_smul, ← co.e.symm.map_zero]
    congr 1
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
  · refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]

theorem at_symp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (AE F E)) (JB : Matrix (Fin d) (Fin d) (AE F E)) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}
    (x u : Matrix (Fin n) (Fin d) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) (symp (R := AF F) (cA σ) (-1) JA JB x u) := by
  intro a ha
  have h := GlobalTheory.LatVac.symp_smul_smul σ JA JB (-1) a 1 x u
  rw [hx a ha, one_smul, mul_one, GlobalTheory.VacIndic.symp_zero_left] at h
  rw [smul_eq_mul]
  exact h.symm

theorem co_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ((1 : GL (Fin n) (Fv F v))⁻¹).1 * u.map (piW t) * ((1 : GL (Fin d) (Fv F v))⁻¹).1ᵀ = u.map (piW t) := by
  simp

theorem exists_isLinW : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∃ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v hv
  obtain ⟨t⟩ := nonempty_emb_of_splitsFully hTr.base.cm v hv.2
  obtain ⟨uT, uM, hT, hM, hspan, hsymp⟩ := (GlobalTheory.T.local_unipotent_embeddings_exist) F E σ B a a' G X om om' hTr v t
  change ∀ (x u : Matrix (Fin a) (Fin (a + a')) (AE F E)),
    At (evFin F v) x → At (evFin F v) u →
    evFin F v (symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
      (incM F G.V.J) (incM F G.W.J) x u) =
      ∑ i, ∑ j, x.map (piW t) i j * coW G t u i j -
        ∑ i, ∑ j, coW G t x i j * u.map (piW t) i j at hsymp
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 v
  have hunr : PsiUnr B.ψ v := GlobalTheory.StdCharUnrF.psiUnr_of_not_le F B.ψ hTr.base.std v
    (GlobalTheory.SplitFullyUnr.not_le_differentIdeal v hv.2)
  have hunr' : ∀ x : Fv F v, (∀ y ∈ 𝒪[Fv F v], GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) ↔
      x ∈ 𝒪[Fv F v] := by
    intro x
    simp only [GlobalTheory.FinPl.SplitPoint.mem_integer_iff]
    exact hunr x
  have hcoT : ∀ Y, coW G t (uT Y) = 0 := fun Y => coW_eq_zero G t _ (hT Y).2.1
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  obtain ⟨ι, hbij, htr, hmu⟩ := _root_.GlobalTheory.StoneVN.intertwiner_matrix (GlobalTheory.LatVac.psiAt B.ψ v) hψc hunr'
    ((GlobalTheory.LatVac.locCo G.M.co v).comp uT) ((GlobalTheory.LatVac.locCo G.M.co v).comp uM)
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form]
      rw [hsymp _ _ (hT Y).1 (hT Y').1, hcoT, hcoT]
      simp)
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form]
      rw [hsymp _ _ (hM z).1 (hM z').1, (hM z).2.1, (hM z').2.1]
      simp)
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form]
      rw [hsymp _ _ (hT Y).1 (hM z).1, (hT Y).2.2, (hM z).2.2, hcoT, (hM z).2.1]
      simp)
    (fun w => by
      obtain ⟨u, hu, rfl⟩ := locCo_surj G.M.co v w
      obtain ⟨Y, z, rfl⟩ := hspan u hu
      exact ⟨Y, z, by simp only [AddMonoidHom.comp_apply, map_add (f := _)]⟩)
  have hφ₁ : ∀ (u : Matrix (Fin a) (Fin (a + a')) (AE F E)), At (evFin F v) u →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin F v) (G.M.co.rho B.ψ u) φ φ₁ →
        φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v u) φ :=
    fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr =>
      (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v u hu φ r hr)
  refine ⟨t, ι, hbij, ?_, ?_⟩
  · intro u hu hu0 φ hφ φ₁ _ hact Y
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hz : z = 0 := by
      have h := hu0
      rw [Matrix.map_add _ (map_add _), (hT Y₀).2.1, zero_add] at h
      rw [← (hM z).2.2]
      exact coW_eq_zero G t _ h
    subst hz
    rw [map_zero, add_zero] at e1 ⊢
    rw [co_one, (hT Y₀).2.2, e1]
    exact congrFun (htr Y₀ φ hφ) Y
  · intro u hu hu1 φ hφ φ₁ _ hact x hx hx0
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hY : Y₀ = 0 := by
      have h := hu1
      rw [Matrix.map_add _ (map_add _), (hM z).2.1, add_zero] at h
      rw [← (hT Y₀).2.2]
      exact h
    subst hY
    rw [map_zero, zero_add] at e1 ⊢
    rw [co_one, e1, GlobalTheory.VacIndic.psi_of_at B.ψ (at_symp _ _ _ x (uM z) hx)]
    rw [hsymp x (uM z) hx (hM z).1,
      coW_eq_zero G t x hx0, (hM z).2.1, (hM z).2.2]
    have h2 := congrFun (hmu z φ hφ) (x.map (piW t))
    simp only [AddMonoidHom.comp_apply] at h2
    rw [h2, ← GlobalTheory.LatVac.psiAt_apply]
    congr 2
    simp

end GlobalTheory.LinWAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFiniteDimensionalFinitePartsWeilTrans
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilContF

theorem adeleJoin_zero_zero (F : Type) [Field F] [NumberField F] (κ : Type) :
    GlobalTheory.WeilCont.adeleJoin F (0 : κ → mixedEmbedding.mixedSpace F) 0 = 0 := by
  funext i
  simp only [GlobalTheory.WeilCont.adeleJoin, Pi.zero_apply, map_zero, Prod.mk_zero_zero]

theorem sum_mul_zero_prod {κ : Type} [Fintype κ] {A B : Type} [CommRing A] [CommRing B] (z : κ → A × B)
    (y : κ → B) : (∑ i, z i * ((0 : A), y i)) = ((0 : A), ∑ i, (z i).2 * y i) := by
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

theorem dotProduct_adeleJoin_zero (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (z : κ → AdeleRing (𝓞 F) F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    z ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y = pairA F 0 ((fun i => (z i).2) ⬝ᵥ y) := by
  simp only [dotProduct, GlobalTheory.WeilCont.adeleJoin, pairA, Pi.zero_apply, map_zero]
  exact sum_mul_zero_prod (A := InfiniteAdeleRing F) (B := FiniteAdeleRing (𝓞 F) F) z y

end GlobalTheory.WeilContF

namespace GlobalTheory.WeilContF

theorem exists_local_finite_parts_F : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
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
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ p0, ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
      (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        om p Φ = ∑ i, pureA F (f i) (g i) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ χS χT hS hT hrS hrT ω hω JA JB ξ hJA hJB κ _ co hco om hom Φ hΦ p0
  obtain ⟨pres, impl⟩ := GlobalTheory.T.transportedWeilDatum_CM_preserves_schwartz_heisenberg F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ χS χT hS hT hrS hrT ω hω JA JB ξ hJA hJB κ co
    hco om hom
  obtain ⟨L₁, L₂, hL₁, hL₂, hinv⟩ := GlobalTheory.T.exists_openSubgroups_schroedinger_fix_continuousChar F B.ψ hB.std.1 κ Φ hΦ
  obtain ⟨N, hN, L₁', L₂', hL₁', hL₁c, hL₂', hNL⟩ := GlobalTheory.T.exists_nhds_transportedAction_finitePoint_preimage F E σ nT nS JA JB ξ κ co L₁ L₂ hL₁ hL₂ p0
  have hK := _root_.GlobalTheory.AnnCompactStd.isCompact_annihilator F B.ψ hB.std κ L₂' hL₂'
  obtain ⟨m, g, y, hg, hgy, hrep⟩ := _root_.GlobalTheory.WeilCont.schA_periodic_finite_cosets F κ L₁' hL₁' hL₁c _ hK
  refine ⟨N, hN, m, g, y, hg, hgy, fun p hp => ?_⟩
  have fix : ∀ x ∈ L₁', ∀ y₁ ∈ L₂', schr B.ψ (GlobalTheory.WeilCont.adeleJoin F 0 x,
      GlobalTheory.WeilCont.adeleJoin F 0 y₁) (om p Φ) = om p Φ := by
    intro x hx y₁ hy₁
    obtain ⟨x', hx', y', hy', he⟩ := hNL p hp x hx y₁ hy₁
    have := impl p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x', GlobalTheory.WeilCont.adeleJoin F 0 y')) Φ hΦ
    simp only [Darboux.rho, LinearEquiv.apply_symm_apply, hinv x' hx' y' hy'] at this
    change co.e (actAB (cA σ) p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x', GlobalTheory.WeilCont.adeleJoin F 0 y'))) =
      (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y₁) at he
    rw [he] at this
    exact this.symm
  refine hrep (om p Φ) (pres p Φ hΦ) ?_ ?_
  · intro x hx z
    have := congrFun (fix x hx 0 (zero_mem _)) z
    simp only [schr, GlobalTheory.WeilContF.adeleJoin_zero_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one,
      one_mul] at this
    exact this
  · intro z hz y₁ hy₁
    have := congrFun (fix 0 (zero_mem _) y₁ hy₁) z
    simp only [schr, GlobalTheory.WeilContF.adeleJoin_zero_zero, zero_dotProduct, mul_zero, add_zero,
      GlobalTheory.WeilContF.dotProduct_adeleJoin_zero] at this
    exact (mul_eq_right₀ hz).mp this

end GlobalTheory.WeilContF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilHomFinitePlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LocalWeilHom

theorem tens_cancel {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ]
    {R : (κ → AF F) → ℂ} (hR : ∀ x z, At (evFin F v) z → R (x + z) = R x) (hR0 : R 0 ≠ 0)
    {φ₁ φ₂ : (κ → Fv F v) → ℂ} (h : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i) with hz
  have hza : At (evFin F v) z :=
    fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (y i) u hu
  have hrx : R (0 + z) = R 0 := hR 0 z hza
  have hy : (fun i => evFin F v ((0 + z) i)) = y := by
    funext i
    simp only [hz, zero_add, GlobalTheory.LatVac.evFin_liftV]
  have e := congrFun h (0 + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ hR0 e

theorem acts_mul {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ]
    (T₁ T₂ : Module.End ℂ ((κ → AF F) → ℂ)) (hT₂ : ∀ Φ ∈ schA F κ, T₂ Φ ∈ schA F κ)
    {φ φ' φ'' : (κ → Fv F v) → ℂ} (h₂ : Acts (evFin F v) T₂ φ φ') (h₁ : Acts (evFin F v) T₁ φ' φ'') :
    Acts (evFin F v) (T₁ * T₂) φ φ'' := by
  intro r hr
  have e₂ := h₂ r hr
  have hr' : Rest (evFin F v) φ' r := ⟨hr.1, by rw [← e₂]; exact hT₂ _ hr.2⟩
  show T₁ (T₂ (tens (evFin F v) φ r)) = _
  rw [e₂]
  exact h₁ r hr'

theorem exists_hom {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ] {Γ : Type} [Monoid Γ]
    (ρ : Γ →* Module.End ℂ ((κ → AF F) → ℂ)) (hpres : ∀ γ, ∀ Φ ∈ schA F κ, ρ γ Φ ∈ schA F κ)
    (hex : ∀ γ, ∀ m ∈ SB (κ → Fv F v), ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (ρ γ) m φ₁) :
    ∃ ω : Γ →* Module.End ℂ (SB (κ → Fv F v)), ∀ γ (m : SB (κ → Fv F v)) (φ₁ : (κ → Fv F v) → ℂ),
      φ₁ ∈ SB (κ → Fv F v) → (Acts (evFin F v) (ρ γ) (m : (κ → Fv F v) → ℂ) φ₁ ↔ ((ω γ m : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ) = φ₁) := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) κ v
  have hRi : ∀ x z, At (evFin F v) z → R (x + z) = R x := (hR 0 (SB _).zero_mem).1
  choose f hfSB hfA using hex

  have hread : ∀ γ (m : (κ → Fv F v) → ℂ) (hm : m ∈ SB (κ → Fv F v)) (φ₁ : (κ → Fv F v) → ℂ),
      Acts (evFin F v) (ρ γ) m φ₁ → ρ γ (tens (evFin F v) m R) = tens (evFin F v) φ₁ R :=
    fun γ m hm φ₁ h => h R (hR m hm)
  have huniq : ∀ γ (m : (κ → Fv F v) → ℂ) (hm : m ∈ SB (κ → Fv F v)) (φ₁ : (κ → Fv F v) → ℂ),
      ρ γ (tens (evFin F v) m R) = tens (evFin F v) φ₁ R → f γ m hm = φ₁ := by
    intro γ m hm φ₁ h
    exact tens_cancel v hRi hR0 ((hread γ m hm _ (hfA γ m hm)).symm.trans h)
  have htadd : ∀ φ φ' : (κ → Fv F v) → ℂ, tens (evFin F v) (φ + φ') R =
      tens (evFin F v) φ R + tens (evFin F v) φ' R := by
    intro φ φ'; funext x; simp only [tens, Pi.add_apply, add_mul]
  have htsmul : ∀ (c : ℂ) (φ : (κ → Fv F v) → ℂ), tens (evFin F v) (c • φ) R = c • tens (evFin F v) φ R := by
    intro c φ; funext x; simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]
  let L : Γ → Module.End ℂ (SB (κ → Fv F v)) := fun γ =>
    { toFun := fun m => ⟨f γ m m.2, hfSB γ m m.2⟩
      map_add' := fun m m' => by
        apply Subtype.ext
        show f γ _ _ = f γ m m.2 + f γ m' m'.2
        apply huniq
        rw [Submodule.coe_add, htadd, map_add (f := _), hread γ m m.2 _ (hfA γ m m.2),
          hread γ m' m'.2 _ (hfA γ m' m'.2), htadd]
      map_smul' := fun c m => by
        apply Subtype.ext
        show f γ _ _ = c • f γ m m.2
        apply huniq
        rw [Submodule.coe_smul, htsmul, map_smul, hread γ m m.2 _ (hfA γ m m.2), htsmul] }
  have hL : ∀ γ (m : SB (κ → Fv F v)), ((L γ m : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ) = f γ m m.2 := fun _ _ => rfl
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply LinearMap.ext; intro m
    apply Subtype.ext
    rw [hL]
    apply huniq
    rw [map_one]; rfl
  · intro γ γ'
    apply LinearMap.ext; intro m
    apply Subtype.ext
    rw [hL]
    show f (γ * γ') m m.2 = f γ (f γ' m m.2) (hfSB γ' m m.2)
    apply huniq
    rw [map_mul]
    exact acts_mul v (ρ γ) (ρ γ') (hpres γ') (hfA γ' m m.2) (hfA γ _ (hfSB γ' m m.2)) R (hR m m.2)
  · intro γ m φ₁ _
    show _ ↔ f γ m m.2 = φ₁
    constructor
    · intro h; exact huniq γ m m.2 φ₁ (hread γ m m.2 φ₁ h)
    · intro h; rw [← h]; exact hfA γ m m.2

end GlobalTheory.LocalWeilHom

namespace GlobalTheory.LocalWeilHom

theorem local_weil_hom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] (σL : L →+* L) (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L)
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      (∀ g, ιS g ∈ UAt σ G.V' (evFin F v)) → (∀ h, ιT h ∈ UAt σ G.W (evFin F v)) →
    ∃ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w _ _ L _ σL JS JT ιS ιT hιS hιT
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  let ρ := om'.comp (MonoidHom.prodMap ιS ιT)
  have hρ : ∀ g h, ρ (g, h) = om' (ιS g, ιT h) := fun _ _ => rfl
  have hpres : ∀ γ, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), ρ γ Φ ∈ schA F (Fin a' × Fin (a + a')) :=
    fun γ Φ hΦ => hW.pres _ Φ hΦ
  have hex : ∀ γ, ∀ m ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (ρ γ) m φ₁ := by
    rintro ⟨g, h⟩ m hm
    obtain ⟨φ₁, hφ₁, hA₁⟩ := GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW F E σ B a a' G X om om' hTr v (ιT h) (hιT h) m hm
    obtain ⟨S, hS⟩ := GlobalTheory.WeilLocality.locality B G X om om' hTr v (ιS g) (hιS g)
    refine ⟨S φ₁, (hS φ₁ hφ₁).1, ?_⟩
    have hsplit : ρ (g, h) = om' (ιS g, 1) * om' (1, ιT h) := by
      rw [hρ, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    rw [hsplit]
    exact acts_mul v _ _ (fun Φ hΦ => hW.pres _ Φ hΦ) hA₁ (hS φ₁ hφ₁).2
  obtain ⟨ω, hω⟩ := exists_hom v ρ hpres hex
  exact ⟨ω, fun g h m φ₁ hφ₁ => hω (g, h) m φ₁ hφ₁⟩

end GlobalTheory.LocalWeilHom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBoundsInertPrime
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem facBetween_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ¬ (p : ℤ) ∣ discr E → InertInK H p → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → ∃ A B : ℝ, FacBetween Xo la f k A B ∧ B - A ≤ boundInert p Dw.q (rk f) k := by
  intro E _ _ _ H Dw l Xo c p _ la hdisc hinert f k hpsi
  letI := H.starRing
  obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.detPow_content_const p Fact.out (rk f) k
  have hFGT := _root_.GlobalTheory.PrimePart.formalGroupTypes E H Dw l Xo c (fun _ => rfl) p hdisc
  have hch : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Nonempty (IntegralChartA3 Xo c T io y) :=
    fun T io y => by
      obtain ⟨C, -⟩ := (@GlobalTheory.IntChartExists.intChart_exists E _ _ _ H Dw l Xo c H.starRing).2.2 (fun _ => rfl) T io y
      exact ⟨C⟩
  have hbd : boundInert p Dw.q (rk f) k =
      2 * ((rk f : ℕ) : ℝ) * (k : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) + 2 * ((Dw.q : ℕ) : ℝ) * (k : ℝ) / ((p : ℝ) - 1) := rfl
  refine ⟨κ - boundInert p Dw.q (rk f) k, κ, fun T io e ho y => ⟨le_nuFac fun Ch X => ?_, fun _ => ?_⟩, by linarith⟩
  · obtain ⟨hfrob, htyp⟩ := hFGT T io X
    obtain ⟨h, hh, -, lab, hlab, d', G', ty, I, P, -, ⟨mu⟩, -, hcard, hfr⟩ := htyp y Ch f.1
    have hf0 : f.1 = lab 0 := hlab.1.symm
    obtain ⟨hsat, hsupp, hnu⟩ := hfr 0 f hf0
    have hiff := (hfrob (lab 0) (lab (0 + 1)) (hlab.2.1 0)).2 hinert
    have hnot : ¬ InPsi H (lab (0 + 1)) := fun h1 =>
      ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.not_inPsi_both H f.1 ⟨hpsi, by rw [hf0]; exact hiff.1 h1⟩
    have hc1 : (Finset.univ.filter fun a => ty a = (0 : ZMod h) + 1).card ≤ Dw.q := by
      have := hcard (0 + 1)
      rw [if_neg hnot, Fintype.card_subtype] at this
      exact this.le
    have hd2 := GlobalTheory.FGDepth.InertBound.content_le_detDepth_add X.C (vX_vp X) p Fact.out (vX_vp_p X) d' h hh ty G' mu
      0 Dw.q (rk f) k hc1 _ hsat hsupp
    rw [hκ X.C (vX_vp X) (vX_vp_p X), ← hbd] at hd2
    rw [hnu k, EReal.coe_sub]
    exact EReal.sub_le_of_le_add hd2
  · obtain ⟨Ch⟩ := hch T io y
    obtain ⟨X⟩ := nonempty_valExt_of_overLa la ho
    have h1 := _root_.GlobalTheory.FGDepth.detDepth_bounds X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) _ k (fgl Ch X) (frame Ch X f)
      (isSatFrame_frame Ch X f)
    refine (nuFac_le Ch X f k).trans ?_
    rw [← hκ X.C (vX_vp X) (vX_vp_p X)]
    exact h1.2.1

end GlobalTheory.RefSum
end

