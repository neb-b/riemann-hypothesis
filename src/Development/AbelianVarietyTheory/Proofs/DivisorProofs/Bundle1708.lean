module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalizingWeightEqualOffPlaceMasses
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantFunctional
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1688
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelConjugateDoubled
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareModel

theorem exists_isGood_model_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (hJ : X.J = (1 : D.host.E) • (spW G i j).gram) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∃ co vac dom, Model.IsGood (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co vac ((M.ν (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))).map (conjU _ 1 hJ)) dom) B.ψ := by
  intro D T L sc G μ₀ _hL t i j M hM B hB X Y hJ r s r' s' hX hY
  obtain ⟨hH, hfd⟩ := (hM.vtx (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).haar_fund
  obtain ⟨hH', hfd'⟩ := _root_.GlobalTheory.ConjUTransport.map_isHaar_isFundamentalDomain _ (1 : D.host.E) one_ne_zero hJ _ _ hH hfd
  obtain ⟨co, hrat⟩ := GlobalTheory.T.exists_rational_darboux_coordinates_tensor_hermitian B hB X Y r s r' s' hX hY
  have hind := GlobalTheory.T.eventually_selfDualLattice_indicator_is_vacuum B hB X Y r s r' s' hX hY co hrat
  have hany := GlobalTheory.T.exists_finitePlace_vacuum_any_darboux_coordinates B hB X Y r s r' s' hX hY co
  let ind : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F v) → ℂ :=
    fun v => Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers D.host.F} 1
  let vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F v) → ℂ :=
    fun v => if Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v (ind v) then ind v
      else (hany v).choose
  refine ⟨co, vac, _, { rat := hrat, vac := fun v => ?_, std := ?_, haar := hH', dom := hfd' }⟩
  · show Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v (vac v)
    by_cases h : Model.IsVac (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v (ind v)
    · simp only [vac, if_pos h]; exact h
    · simp only [vac, if_neg h]; exact (hany v).choose_spec
  · filter_upwards [hind] with v hv
    show vac v = ind v
    exact if_pos hv

end GlobalTheory.SquareModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianInvariantFormInertVacuum
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertVacLagP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_map_compFin (v : Pl (F := F)) {d m : ℕ} (Cy : Matrix (Fin d) (Fin m) (Fv F v ⊗[F] E)) :
    ∃ C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), C.map (compFin F E v) = Cy := by
  have hs : Function.Surjective (compFin F E v) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul x e =>
      refine ⟨GlobalTheory.LatVac.liftV v x ⊗ₜ e, ?_⟩
      simp [compFin, GlobalTheory.LatVac.evFin_liftV]
    | add x y hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      exact ⟨p + q, by rw [map_add (f := _), hp, hq]⟩
  choose f hf using hs
  exact ⟨Cy.map f, by ext i j; simp [hf]⟩

def lagSub {n d m : ℕ} (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : AddSubgroup (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) where
  carrier := GlobalTheory.InertVacLag.lagAt v C
  zero_mem' := ⟨fun u _ => smul_zero u, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, z, rfl⟩ ⟨hy, z', rfl⟩
    exact ⟨fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero], z + z', by rw [Matrix.add_mul]⟩
  neg_mem' := by
    rintro x ⟨hx, z, rfl⟩
    exact ⟨fun u hu => by rw [smul_neg, hx u hu, neg_zero], -z, by rw [Matrix.neg_mul]⟩

theorem acts_unique {κ : Type} [Fintype κ] (v : Pl (F := F)) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (φ φ₁ φ₂ : (κ → Fv F v) → ℂ) (hφ : φ ∈ SB (κ → Fv F v)) (h1 : Acts (evFin F v) T φ φ₁)
    (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  have e := (h1 R (hR φ hφ)).symm.trans (h2 R (hR φ hφ))
  funext y
  have hy := congrFun e (fun i => GlobalTheory.LatVac.liftV v (y i))
  simp only [tens] at hy
  have hev : (fun i => evFin F v (GlobalTheory.LatVac.liftV v (y i))) = y := funext fun i => GlobalTheory.LatVac.evFin_liftV v (y i)
  rw [hev] at hy
  have hRx : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by
    have := (hR φ hφ).1 0 (fun i => GlobalTheory.LatVac.liftV v (y i)) (fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (y i) u hu)
    simpa using this
  rw [hRx] at hy
  exact mul_right_cancel₀ hR0 hy

theorem eq_of_locCo {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux Bf κ) (v : Pl (F := F)) (g u : W) (hg : At (evFin F v) g) (hu : At (evFin F v) u)
    (h : GlobalTheory.LatVac.locCo co v g = GlobalTheory.LatVac.locCo co v u) : g = u := by
  have hA : ∀ z : W, At (evFin F v) z → ∀ k, At (evFin F v) ((co.e z).1 k) ∧ At (evFin F v) ((co.e z).2 k) := by
    intro z hz k
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have := congrArg (fun p => p.1 k) (show co.e (t • z) = t • co.e z from co.e.map_smul t z)
      simpa [hz t ht] using this.symm
    · have := congrArg (fun p => p.2 k) (show co.e (t • z) = t • co.e z from co.e.map_smul t z)
      simpa [hz t ht] using this.symm
  apply co.e.injective
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · rw [GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA g hg k).1, GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA u hu k).1]
    exact congrArg _ (congrFun h1 k)
  · rw [GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA g hg k).2, GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA u hu k).2]
    exact congrArg _ (congrFun h2 k)

theorem exists_lagr_inv_vac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (C : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      GlobalTheory.InertVacLag.IsLagrAt σ G.W v C ∧ GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l ∧ l (G.M'.vac v) ≠ 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin _
  obtain ⟨Cy, hCy⟩ := GlobalTheory.InertLagr.exists_lagr F E σ B a a' G X om om' hT v w hin
  obtain ⟨C, hC⟩ := exists_map_compFin (E := E) v Cy
  have hLag : GlobalTheory.InertVacLag.IsLagrAt σ G.W v C := by
    unfold GlobalTheory.InertVacLag.IsLagrAt; rw [hC]; exact hCy
  set co := G.M'.co with hco
  set Λ := (lagSub (n := a') v C).map (GlobalTheory.LatVac.locCo co v) with hΛ
  set Γ := (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo co v) with hΓ
  have hgood := hT.base.inert v w hin
  obtain ⟨hsb, hne, θ, hθ, hvac⟩ := hT.geo.hM'.vac v
  have hatL := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := hT.base.std.1.comp (GlobalTheory.VacAny.continuous_atPlace v)
  have hψ : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) →
      x ∈ v.adicCompletionIntegers F := fun x hx => (hgood.2.2 x).1 hx
  have hiso : ∀ x ∈ Λ, ∀ x' ∈ Λ, x.1 ⬝ᵥ x'.2 - x'.1 ⬝ᵥ x.2 = 0 := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    have h0 := GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ G.V'.J G.W v C hLag (-1) u u' hu hu'
    change symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) u u' = 0 at h0
    rw [co.form] at h0
    have h1 := congrArg (evFin F v) h0
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub] using h1
  have hOC := GlobalTheory.LatOpenCpt.main σ B G.V' G.W _ _ _ _ hT.geo.hV' hT.geo.hW G.M' hT.geo.hM'.rat v
  have hdual := GlobalTheory.LatVac.DualLoc.map_selfDual v co B.ψ (latAtV G.V' G.W v) hatL
    (GlobalTheory.T.inertPlace_tensorLattice_selfDual_supportedAt F E σ B a a' G X om om' hT v w hin)
  have heig0 : ∀ g ∈ latAtV G.V' G.W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo co v g) (G.M'.vac v) =
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) g g) • G.M'.vac v :=
    fun g hg => acts_unique v _ _ _ _ hsb (GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v g (hatL g hg) _) (hvac g hg)
  have heig : ∀ γ ∈ Γ, ∃ c : ℂ, schr (GlobalTheory.LatVac.psiAt B.ψ v) γ (G.M'.vac v) = c • G.M'.vac v := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨_, heig0 g hg⟩
  have hfix : ∀ γ ∈ Γ ⊓ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) γ (G.M'.vac v) = G.M'.vac v := by
    rintro γ ⟨⟨g, hg, rfl⟩, ⟨u, hu, hgu⟩⟩
    have e : g = u := eq_of_locCo co v g u (hatL g hg) hu.1 hgu.symm
    subst e
    rw [heig0 g hg, GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ G.V'.J G.W v C hLag _ g g hu hu, mul_zero, AddChar.map_zero_eq_one, one_smul]
  obtain ⟨l, hl, hl0⟩ := GlobalTheory.T.lagrangian_invariant_linearForm_local_uniqueness v (GlobalTheory.LatVac.psiAt B.ψ v) (Fin a' × Fin (a + a')) Λ Γ (G.M'.vac v) hψc hψ hiso
    hOC.1 hOC.2 hdual hsb hne heig hfix
  refine ⟨C, l, hLag, ?_, hl0⟩
  intro u hu φ hφ φ₁ _ hA
  have e := acts_unique v _ φ φ₁ _ hφ hA (GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v u hu.1 φ)
  rw [e]
  exact hl _ ⟨u, hu, rfl⟩ φ hφ

end GlobalTheory.InertVacLagP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVacuumFinitePlacesRationalDarbouxStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeVacuum_finitePlaces_rationalDarboux : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ M : Model σ X Y, (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
      ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ φ : (Fin n × Fin d → Fv F v) → ℂ, M.IsVac B.ψ v φ := by
  first | exact @GlobalTheory.LatVac.exists_isVac | exact GlobalTheory.LatVac.exists_isVac | (intros; apply GlobalTheory.LatVac.exists_isVac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
section
noncomputable section

namespace GlobalTheory.ThK.LemF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsLocPart {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ) : Prop :=
  ei ≠ 0 ∧ (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
    ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)

end GlobalTheory.ThK.LemF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalizingWeightEqualOffPlaceMassesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localizingWeight_equal_offPlaceMasses : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ,
    (∀ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) →
      ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x‖ₑ ^ 2 ∂μ) →
    ∀ (y : κ → AF F) (O : Set (κ → AF F)), IsOpen O → y ∈ O →
    ∃ h : (κ → AF F) → ENNReal, @Measurable _ _ (borel _) _ h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, GlobalTheory.LatVac.liftV v 1 • z = z → h (x + z) = h x) ∧
      (∀ x, h x ≠ 0 → x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x) ∈ O) ∧
      (∃ O' : Set (κ → AF F), IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.OffVLocalWeights.exists_localizing_weight | exact GlobalTheory.OffVLocalWeights.exists_localizing_weight | (intros; apply GlobalTheory.OffVLocalWeights.exists_localizing_weight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroPrimitiveFrameDatumRenumber
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section
namespace GlobalTheory.ColumnRenumber

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' C : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]

def permGL (π : C ≃ C) : GL C k :=
  ⟨π.toPEquiv.toMatrix, π.symm.toPEquiv.toMatrix,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq A] [DecidableEq A'] in
theorem frameMatrixFirstColumnBlock_renumber (σ σ' : A ⊕ A' ≃ C) (h : GL C k) :
    X0 k σ' * (invT h).val = X0 k σ * (invT (permGL (σ.symm.trans σ') * h)).val := by
  ext i j
  rw [frameMatrixFirstColumnBlock_mul_apply, frameMatrixFirstColumnBlock_mul_apply, invT_val, invT_val, _root_.mul_inv_rev]
  simp [permGL, Matrix.mul_apply, PEquiv.toMatrix_apply, Units.val_mul, Option.mem_def, Equiv.symm_apply_eq]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq A] [DecidableEq A'] in
theorem frameMatrixSecondColumnBlock_renumber (σ σ' : A ⊕ A' ≃ C) (h : GL C k) :
    Y0 k σ * (permGL (σ.symm.trans σ') * h).val = Y0 k σ' * h.val := by
  ext i j
  rw [frameMatrixSecondColumnBlock_mul_apply, frameMatrixSecondColumnBlock_mul_apply]
  simp [permGL, Matrix.mul_apply, PEquiv.toMatrix_apply, Units.val_mul]

variable [MeasurableSpace k] [BorelSpace k]

theorem fFun_renumber (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ σ' : A ⊕ A' ≃ C) (ν : kˣ →* ℂˣ)
    (Ψ : Matrix A' C k → ℂ) (X : Matrix A C k) :
    fFun μ σ' ν Ψ X = ((ν (gdet (permGL (k := k) (σ.symm.trans σ'))) : ℂ) *
      apow (gdet (permGL (k := k) (σ.symm.trans σ'))) ((Fintype.card C : ℂ) / 2))⁻¹ * fFun μ σ ν Ψ X := by
  set Q : GL C k := permGL (σ.symm.trans σ') with hQ
  by_cases hX : ∃ h : GL C k, X = X0 k σ' * (invT h).val
  · obtain ⟨h, rfl⟩ := hX
    have hc : (ν (gdet Q) : ℂ) * apow (gdet Q) ((Fintype.card C : ℂ) / 2) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
    rw [splitTheta_fFun_frameFirstBlock_mul μ σ', frameMatrixFirstColumnBlock_renumber σ σ' h, splitTheta_fFun_frameFirstBlock_mul μ σ, ← hQ, frameMatrixSecondColumnBlock_renumber, gdet_mul, map_mul, apow_mul,
      Units.val_mul]
    have ha := apow_ne_zero (gdet Q) ((Fintype.card C : ℂ) / 2)
    have hn : (ν (gdet Q) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  · have hX' : ¬ ∃ h : GL C k, X = X0 k σ * (invT h).val := fun H =>
      hX ((rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ' X).1 ((rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).2 H))
    rw [fFun, dite_eq_right hX, fFun, dite_eq_right hX', mul_zero]

end GlobalTheory.ColumnRenumber


open GlobalTheory.ColumnRenumber in
theorem GlobalTheory.ColumnRenumber.phiA_renumber : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (A A' C : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ σ' : A ⊕ A' ≃ C) (ν : kˣ →* ℂˣ),
    ∃ u : ℂ, u ≠ 0 ∧ ∀ (ϖ : kˣ) (n : ℕ) (Λ : Submodule 𝒪[k] (C → k)) (Ψ : Matrix A' C k → ℂ) (X : Matrix A C k),
      phiA μ σ' ν ϖ n Λ Ψ X = u * phiA μ σ ν ϖ n Λ Ψ X := by
  intro k _ _ _ _ _ _ A A' C _ _ _ _ _ _ μ _ σ σ' ν
  refine ⟨((ν (gdet (permGL (k := k) (σ.symm.trans σ'))) : ℂ) *
      apow (gdet (permGL (k := k) (σ.symm.trans σ'))) ((Fintype.card C : ℂ) / 2))⁻¹,
    inv_ne_zero (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)), fun ϖ n Λ Ψ X => ?_⟩
  unfold phiA
  split_ifs
  · exact fFun_renumber μ σ σ' ν Ψ X
  · rw [mul_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatFamOfIsDiscrete
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem exists_satFam_of_isDiscrete : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), (∀ x : CuspSub E N, ∀ᶠ v in Filter.cofinite, ∃ C, (CG.mk x).HasSat v C) ∧ ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∃ B, SatFam V B := by
  intro E _ _ _ N
  have hF := GlobalTheory.automorphicFormsFiniteGL
  refine ⟨fun x => UnrSat.eventually_hasSatGL_locRep hF E N x, fun V hV => ?_⟩
  choose σ hσ using GlobalTheory.DiscLocEx.exists_isLocCompGL hF E N V hV
  have h : ∀ w, ∃ B, GlobalTheory.LGrp.IsSpherical (σ w).ρ (GlobalTheory.LFun.KGL w (n := N)) → GlobalTheory.LFun.HasSatGL w (σ w).ρ B := fun w => by
    by_cases hs : GlobalTheory.LGrp.IsSpherical (σ w).ρ (GlobalTheory.LFun.KGL w (n := N))
    · obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible (σ w).smooth (σ w).irred hs
      exact ⟨B, fun _ => hB⟩
    · exact ⟨0, fun h => absurd h hs⟩
  choose B hB using h
  refine ⟨B, fun φ hφ h0 => ?_⟩
  filter_upwards [GlobalTheory.SpehPair.eventually_spherical hV,
    LocSph.eventually_mem ((hV.aut φ hφ).level.mem_nhds (by simp))] with w hw hK
  refine GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup (σ w).irred (hB w (hw _ (hσ w)))
    (fun f : GlobalTheory.LocDual.Maps V w (σ w) => f.1) (fun f => f.2.2) ?_ (GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_) h0
  · rw [GlobalTheory.LocDual.iSup_range_eq V hV.stable hV.irred w (σ w) (hσ w)]
    exact hφ
  · obtain ⟨g, rfl⟩ := hk
    exact hK g

end GlobalTheory.ResW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantFunctionalStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translation_invariant_functional : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (n d : ℕ), ∃ Λ : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), ∀ a, Λ (fun Y => f (Y + a)) = Λ f) ∧
      ∃ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), Λ f ≠ 0 := by
  first | exact @GlobalTheory.HaarSB.exists_invariant_form_matrix | exact GlobalTheory.HaarSB.exists_invariant_form_matrix | (intros; apply GlobalTheory.HaarSB.exists_invariant_form_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupLevelStructureActionFixedRunsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteGroup_levelStructure_action_fixedRuns : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → (∀ i, OMPins J R κ v₀ O i) → RhoGeo fw O → (∀ i, OneMapRow0 J R κ v₀ O i) → J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∃ ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l), ∀ (r : RunData J) (h : LawsFull r.full) (i : Fin D.R.m), letI : Algebra r.full.J.Q.c.F D.what₂.LL := ‹Algebra J.Q.c.F D.what₂.LL›; LevelPin (T := r.full) R i (ℓ i) ∧ ActionPin (T := r.full) (R := R) h.p fw i (ℓ i) := by
  first | exact @GlobalTheory.LevelActionOnto.levelPin_actionPin | exact GlobalTheory.LevelActionOnto.levelPin_actionPin | (intros; apply GlobalTheory.LevelActionOnto.levelPin_actionPin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSurjectiveExtendsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_eigen_surjective_extends : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, Set.SurjOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) → (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → Function.Surjective ei := by
  first | exact @GlobalTheory.ArchSurj.surjective_arch | exact GlobalTheory.ArchSurj.surjective_arch | (intros; apply GlobalTheory.ArchSurj.surjective_arch <;> assumption)
end

