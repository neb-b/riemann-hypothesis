module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledWeilSplitPlaceVacuumEigenfunction
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0746
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0005
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicStripSetMeasurableReadOnRealPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledWeilSplitPlaceVacuumEigenfunctionStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeil_split_place_vacuum_eigenfunction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T → PsiUnr B.ψ v →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  first | exact @GlobalTheory.DblVacAny.split_eigen | exact GlobalTheory.DblVacAny.split_eigen | (intros; apply GlobalTheory.DblVacAny.split_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlaceUnitaryPointKeepsZeroMatchedData
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKerFin

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem polZero_om_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v),
    ∀ Φ, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (1, h) Φ) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v h hh Φ hΦ
  classical
  obtain ⟨T, hXT, m, f, φ, hf, rfl, hz⟩ := hΦ
  have hP := GlobalTheory.ThK.RealUniq.isPair_V hM.triple
  have h1 : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := by
    intro u _
    show u • ((1 : UA σ G.V.J).1.1 - 1) = 0
    simp
  have hex : ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ₀ φ₁ :=
    fun φ₀ hφ₀ => GlobalTheory.ThK.LocalOps.acts_exists hP v (1, h) h1 hh φ₀ hφ₀
  choose D hDSB hDA using hex
  have hex' : ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ₀ φ₁ := fun φ₀ hφ₀ => ⟨D φ₀ hφ₀, hDSB φ₀ hφ₀, hDA φ₀ hφ₀⟩
  let Dl : SB (Fin a × Fin (a + a') → Fv F v) →ₗ[ℂ] SB (Fin a × Fin (a + a') → Fv F v) :=
    { toFun := fun x => ⟨D x.1 x.2, hDSB x.1 x.2⟩
      map_add' := fun x y => by
        apply Subtype.ext
        have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) hex' x.2 y.2 (hDA x.1 x.2) (hDA y.1 y.2) 1 1
        simp only [one_smul] at hl
        exact GlobalTheory.ThK.LocalOps.acts_unique v _ (x + y).2 (hDA _ (x + y).2) hl
      map_smul' := fun c x => by
        apply Subtype.ext
        have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) hex' x.2 x.2 (hDA x.1 x.2) (hDA x.1 x.2) c 0
        simp only [zero_smul, add_zero] at hl
        exact GlobalTheory.ThK.LocalOps.acts_unique v _ (c • x).2 (hDA _ (c • x).2) hl }
  let π : SB (Fin a × Fin (a + a') → Fv F v) →ₗ[ℂ] Rf.Pi v := (Rf.p v).comp (SB _).subtype
  have hsurj : Function.Surjective π := by
    intro y
    have hy : y ∈ (SB _).map (Rf.p v) := (hM.fin.onto v).symm ▸ Submodule.mem_top
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hA0 : Acts (evFin F v) (om' (1, h)) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) 0 := by
    intro r _
    have e : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext y; simp [tens]
    rw [e, map_zero]
  have hD : ∀ x, π x = 0 → π (Dl x) = 0 := by
    intro x hx
    have e := hM.fin.equiv v h hh x.1 x.2 0 (zero_mem _) (D x.1 x.2) (hDSB x.1 x.2) 0 (zero_mem _) (hDA x.1 x.2) hA0
      (by rw [map_zero]; exact hx)
    rw [map_zero] at e
    exact e
  let L : Rf.Pi v →ₗ[ℂ] Rf.Pi v := GlobalTheory.ThK.RealUniq.induced π hsurj Dl hD
  let ψ : Fin m → (Fin a × Fin (a + a') → Fv F v) → ℂ := fun i => D (φ i v) ((hf i).2.1 v)
  have hL : ∀ i, L (Rf.p v (φ i v)) = Rf.p v (ψ i) := fun i =>
    GlobalTheory.ThK.RealUniq.induced_apply π hsurj Dl hD ⟨φ i v, (hf i).2.1 v⟩
  let φ₂ : Fin m → ∀ w : Pl F, (Fin a × Fin (a + a') → Fv F w) → ℂ := fun i => Function.update (φ i) v (ψ i)
  have hstd : ∀ i, ∀ᶠ w in Filter.cofinite, φ i w = Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1 := by
    intro i
    filter_upwards [hM.triple.geo.hM.std, T.finite_toSet.compl_mem_cofinite] with w hw hwT
    rw [(hf i).2.2 w hwT, hw]
  have hpure : ∀ i, om (1, h) (pure (f i) (φ i)) = pure (f i) (φ₂ i) := by
    intro i
    obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v (f i) (φ i) (hstd i)
    have e1 : pure (f i) (φ i) = tens (evFin F v) (φ i v) r := by
      rw [hrt, Function.update_eq_self]
    have hRest : Rest (evFin F v) (φ i v) r :=
      ⟨hr, by rw [← e1]; exact GlobalTheory.TensUniq.pure_mem_schA _ _ (hf i).2.1 (hstd i)⟩
    rw [e1, hDA _ _ r hRest, hrt]
  have hv : v ∈ insert v T := Finset.mem_insert_self _ _
  have hTS : T ⊆ insert v T := Finset.subset_insert _ _
  refine ⟨insert v T, hXT.trans hTS, m, f, φ₂, fun i => ⟨(hf i).1, fun w => ?_, fun w hw => ?_⟩, ?_, ?_⟩
  · by_cases hwv : w = v
    · subst hwv
      simp only [φ₂, Function.update_self]
      exact hDSB _ _
    · simp only [φ₂, Function.update_of_ne hwv]
      exact (hf i).2.1 w
  · rw [Finset.mem_insert, not_or] at hw
    simp only [φ₂, Function.update_of_ne hw.1]
    exact (hf i).2.2 w hw.2
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => hpure i
  · have hz' := GlobalTheory.PolMatchLin.transport Bs G Xc om om' R Rf hM.fin hXT hTS f φ
      (fun j : Fin 0 => j.elim0 : Fin 0 → SInf F (Fin a' × Fin (a + a')))
      (fun j : Fin 0 => j.elim0 : Fin 0 → ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ)
      (fun i => (hf i).2.2) (fun j => j.elim0) (by rw [hz]; simp)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hz'
    let Lw : ∀ u : (insert v T : Finset (Pl F)), Rf.Pi u →ₗ[ℂ] Rf.Pi u :=
      Function.update (fun _ => LinearMap.id) ⟨v, hv⟩ L
    have key := congrArg (LinearMap.lTensor R.Pi (PiTensorProduct.map Lw)) hz'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at key
    rw [← key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.lTensor_tmul, PiTensorProduct.map_tprod]
    congr 2
    funext u
    by_cases hu : u = ⟨v, hv⟩
    · subst hu
      simp only [Lw, φ₂, Function.update_self]
      exact (hL i).symm
    · have hu' : u.1 ≠ v := fun e => hu (Subtype.ext e)
      simp only [Lw, φ₂, Function.update_of_ne hu, Function.update_of_ne hu', LinearMap.id_apply]

end GlobalTheory.PolKerFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupportUnitaryPointReplacesPureTensorFacto
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.PlaceProd

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n}

theorem mat_injOne (g : UA σ X.J) (h : mat g = 1) : g = 1 := Subtype.ext (Units.ext h)

theorem mat_mul' (g k : UA σ X.J) : mat (g * k) = mat g * mat k := rfl

theorem mat_one' : mat (1 : UA σ X.J) = 1 := rfl

theorem mat_inv_mul' (g : UA σ X.J) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul', inv_mul_cancel, mat_one']

theorem one_mem_UAt {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  rw [mat_one', sub_self, smul_zero]

end GlobalTheory.PlaceProd


open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaceProd GlobalTheory.AdelicU in
theorem GlobalTheory.PlaceProd.pure_of_finSupp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (gS : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J),
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ,
        (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ∧ (∀ v ∉ S, φ' v = φ v) ∧
        (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v) ∧
        om (gS, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' := by
  classical
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP S
  have hstd := hP.good.std
  induction S using Finset.induction_on with
  | empty =>
    intro gS hgS f φ hSB _
    have h1 : mat gS = 1 := by
      have := hgS 1 (by simp)
      rwa [one_smul, sub_eq_zero] at this
    have hg : gS = 1 := mat_injOne gS h1
    refine ⟨φ, hSB, fun _ _ => rfl, fun v => by simp, ?_⟩
    subst hg
    rw [show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one]
    rfl
  | @insert v S' hv ih =>
    intro gS hgS f φ hSB hvac
    obtain ⟨g1, k, hgk, h2, h3, -, -⟩ := GlobalTheory.T.exists_adelicUnitary_factor_finiteSetOfPlaces σ X gS {v}
    have hg1 : g1 ∈ UAt σ X (evFin F v) := fun u hu =>
      h2 u (fun w hw => by rw [Finset.mem_singleton.1 hw]; exact hu)
    have hk : ∀ u : AF F, (∀ w ∈ S', evFin F w u = 0) → u • (mat k - 1) = 0 := by
      intro u hu
      set e : AF F := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he
      have hsplit : u = e * u + (1 - e) * u := by ring
      have ha : (e * u) • (mat k - 1) = 0 := by
        apply h3 v (Finset.mem_singleton_self v)
        rw [he, GlobalTheory.ThK.LocalOps.liftV_one_mul]
        intro u' hu'
        exact GlobalTheory.LatVac.at_liftV v _ u' hu'
      have hb : ((1 - e) * u) • (mat k - 1) = 0 := by
        set u' : AF F := (1 - e) * u with hu'def
        have hv' : evFin F v u' = 0 := by
          simp [hu'def, he, map_mul, map_sub, GlobalTheory.LatVac.evFin_liftV]
        have hS : u' • (mat gS - 1) = 0 := hgS u' (by
          intro w hw
          rcases Finset.mem_insert.1 hw with rfl | hw
          · exact hv'
          · simp [hu'def, map_mul, hu w hw])
        have hg1' : u' • (mat g1 - 1) = 0 := hg1 u' hv'
        have hkk : k = g1⁻¹ * gS := by rw [hgk, inv_mul_cancel_left]
        have hkdef : mat k - 1 = mat g1⁻¹ * (mat gS - 1) - mat g1⁻¹ * (mat g1 - 1) := by
          rw [hkk, mat_mul', Matrix.mul_sub, Matrix.mul_sub, mat_inv_mul', Matrix.mul_one]
          abel
        rw [hkdef, smul_sub, ← Matrix.mul_smul, ← Matrix.mul_smul, hS, hg1', Matrix.mul_zero, sub_self]
      rw [hsplit, add_smul, ha, hb, add_zero]
    obtain ⟨φ₁, hSB1, hoff1, haug1, hom1⟩ := ih k hk f φ hSB hvac
    obtain ⟨φ₂, hSB2, hact⟩ :=
      GlobalTheory.ThK.LocalOps.acts_exists hP v (g1, 1) hg1 (one_mem_UAt (evFin F v)) (φ₁ v) (hSB1 v)
    have hnot : ∀ᶠ w in Filter.cofinite, w ∉ S' :=
      Filter.eventually_cofinite.2 (S'.finite_toSet.subset fun x hx => by simpa using hx)
    have hstd1 : ∀ᶠ w in Filter.cofinite,
        φ₁ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
      filter_upwards [hvac, hstd, hnot] with w h1 h2 h3
      rw [hoff1 w h3, h1, h2]
    have hpure := GlobalTheory.TensUniq.pure_mem_schA f φ₁ hSB1 hstd1
    have hstep := GlobalTheory.ThK.LocalOps.acts_pure v (om (g1, 1)) f φ₁ φ₂ hpure
      (GlobalTheory.PureFactor.mulSupport_finite φ₁ hstd1) hact
    refine ⟨Function.update φ₁ v φ₂, ?_, ?_, ?_, ?_⟩
    · intro w
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hSB2
      · rw [Function.update_of_ne hw]; exact hSB1 w
    · intro w hw
      have hwv : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self _ _)
      have hwS : w ∉ S' := fun h => hw (Finset.mem_insert_of_mem h)
      rw [Function.update_of_ne hwv]; exact hoff1 w hwS
    · intro w
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self, ← hoff1 w hv]
        exact Submodule.subset_span ⟨g1, hg1, φ₁ w, hSB1 w, φ₂, hSB2, hact, rfl⟩
      · rw [Function.update_of_ne hw]; exact haug1 w
    · rw [hgk, show ((g1 * k, 1) : UA σ X.J × UA σ W.J) = (g1, 1) * (k, 1) by simp, map_mul,
        Module.End.mul_apply, hom1, hstep]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointEqUnipotentFrameChangeCosetRepStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_point_eq_unipotent_frame_change_coset_rep : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i)) (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩),
        ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
        ∀ (k' : (T.U ((i : ℕ) + 1) σ).Comp) (x' : ((T.U ((i : ℕ) + 1) σ).X k').dom) (t' : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
          FrBor t' ((T.U ((i : ℕ) + 1) σ).un k' x') z →
        ∀ (gam : ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).Λ →ₗ[𝓞 D.host.E] ((T.U ((i : ℕ) + 1) σ).X k').Λ) (A : (D.host.E →+* ℂ) → ℕ → ℕ → ℂ),
          (∀ u v : ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).Λ, Algebra.trace ℚ D.host.E (-((T.U ((i : ℕ) + 1) σ).X k').ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm ((T.U ((i : ℕ) + 1) σ).X k').Gm (gam u : Fin D.R.r → D.host.E) (gam v : Fin D.R.r → D.host.E)) =
            (p : ℚ) ^ 2 * Algebra.trace ℚ D.host.E (-((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).Gm (u : Fin D.R.r → D.host.E) (v : Fin D.R.r → D.host.E))) →
          (∀ w : ((T.U ((i : ℕ) + 1) σ).X k').Λ, ∃ v, gam v = (p ^ 2) • w) →
          (∀ τ a b, b < a → A τ a b = 0) →
          (∀ τ, ∀ n < (T.Q.Dw ((i : ℕ) + 1)).mult τ, ∀ v : ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).Λ,
            perFr ((T.U ((i : ℕ) + 1) σ).X k') x'.1 (gam v : Fin D.R.r → D.host.E) (relab T.Q.c σ τ) n =
              p * ∑ b ∈ Finset.range ((T.Q.Dw ((i : ℕ) + 1)).mult τ), A τ n b * perFr ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 (v : Fin D.R.r → D.host.E) (relab T.Q.c σ τ) b) →
          (∀ τ (n : Fin ((T.Q.Dw ((i : ℕ) + 1)).mult τ)), A τ n n = toC (t' (some ⟨τ, n⟩) : CAt σ)) →
          ∃ a ∈ Rc, ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
            (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z := by
  first | exact @GlobalTheory.HeckePointCoset.exists_coset_frBor | exact GlobalTheory.HeckePointCoset.exists_coset_frBor | (intros; apply GlobalTheory.HeckePointCoset.exists_coset_frBor <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralStripEqZeroOfRealModulationVanishing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.StripVanish

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y]

theorem dualPair_action_embedded_hyperbolic_extY (d : HypDec V V₀ ρ) (g : GA D V₀) (h : GA D W) (c : Mx D W.rank ρ) :
    actO V W (d.emb0 g) h (d.extY W c) = d.extY W (Formalism.L2.Theta.mt W h ⬝ c) := by
  simp only [actO]
  rw [show (d.emb0 g)⁻¹ = d.emb0 g⁻¹ from (map_inv _ _).symm]
  simp only [ HypDec.extY, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_assoc, HypDec.wittDecomp_projY_anisotropicEmbedding]

theorem symplO_extX_extY_mt (d : HypDec V V₀ ρ) (h : GA D W) (x c : Mx D W.rank ρ) :
    symplO V W (d.extX W x) (d.extY W (Formalism.L2.Theta.mt W h ⬝ c)) =
      symplO V W (d.extX W (Formalism.L2.Theta.mt W h⁻¹ ⬝ x)) (d.extY W c) := by
  rw [← GlobalTheory.SplitHecke.symplO_actO V W 1 h⁻¹]
  congr 1
  · simp only [actO, HypDec.extX, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one, Matrix.mul_assoc]
  · simp only [actO, HypDec.extY, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]

theorem tot_heisO_extY (a : Gen ψ V V₀ W ρ Y) (ha : a.Is) (G : GA D W → ℂ) (Φ : WO V W → ℂ) (hΦ : IsThetaFunO ψ V W Φ)
    (c : Mx D W.rank ρ) (p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank) :
    a.tot G (heisO ψ V W (a.d.extY W c) Φ) p =
      ψ (symplO V W (a.d.extX W (Formalism.L2.Theta.mt W p.1.1⁻¹ ⬝ ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1))) (a.d.extY W c)) *
        a.tot G Φ p := by
  simp only [Gen.tot, flFun]
  rw [ha.weil.om_heis _ _ _ _ hΦ, dualPair_action_embedded_hyperbolic_extY]
  have h := congrFun ((@GlobalTheory.HeisMixSource.heis_mixS D ψ ha.weil.std V V₀ W ρ a.d a.vS (a.om (a.d.emb0 (a.g p.1.2), p.1.1) Φ) (ha.weil.om_pres (a.d.emb0 (a.g p.1.2), p.1.1) Φ hΦ)).2.1
    ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1) (Formalism.L2.Theta.mt W p.1.1 ⬝ c)) (rat a.x₀ ⬝ p.2.2)
  simp only [Pi.smul_apply, smul_eq_mul] at h
  dsimp only [I195MixedCoordinates_5a743adb4eaabe3d936622f8.source] at h
  dsimp only [I195MixedCoordinates_f1b992d3c44b213cc9f27f15.source]
  rw [h, symplO_extX_extY_mt]
  ring

def pointHU (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (q : GA D W × UX D ρ) : Mx D W.rank ρ :=
  Formalism.L2.Theta.mt W q.1⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ q.2.1.1)

theorem measurable_pointHU (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) : Measurable (pointHU (W := W) x₀) := by
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D W.rank ρ) := ⟨rfl⟩
  haveI : SecondCountableTopologyEither (GA D W) (UX D ρ) := secondCountableTopologyEither_of_left _ _
  haveI : OpensMeasurableSpace (GA D W × UX D ρ) := Prod.opensMeasurableSpace
  exact (((continuous_mt W).comp continuous_fst.inv).matrix_mul
      (continuous_const.matrix_mul (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)))).measurable

theorem measurable_point (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) :
    Measurable fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
      Formalism.L2.Theta.mt W p.1.1⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1) := by
  have h1 : Measurable fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => (p.1.1, p.2.1) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  have h2 : Measurable (pointHU (W := W) x₀ ∘ fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => (p.1.1, p.2.1)) :=
    Measurable.comp (measurable_pointHU x₀) h1
  exact h2

end GlobalTheory.StripVanish


open GlobalTheory.StripVanish in
theorem GlobalTheory.StripVanish.integral_strip_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y), a.Is → ∀ (G : GA D W → ℂ), RapidDec W G → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → (∀ c : Mx D W.rank ρ, c.map (finPart D) = 0 → a.lhs G (heisO ψ V W (a.d.extY W c) Φ) = 0) → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ → ∀ C : Set (GA D W), IsCompact C → C ⊆ GinfC W → ∫ h in 𝓑 ∩ strip W (Rgrp W (rat a.x₀)) C, a.ker G Φ h ∂a.vW.μ = 0 := by
  intro D ψ V V₀ W ρ Y _ _ _ _ a ha G hG Φ hΦ hvan 𝓑 h𝓑 C hC hCinf
  obtain ⟨hSmeas, S, hS, hSinf, hSiff⟩ := _root_.GlobalTheory.StripBorel.strip_measurable D W ρ a.x₀ ha.base C hC hCinf
  obtain ⟨hint, -, -, hres⟩ := _root_.GlobalTheory.Asc.unfold_family D ψ V V₀ W ρ Y a ha G Φ hG hΦ 𝓑 h𝓑
  rw [hres _ hSmeas]
  have hpre : {p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank | p.1.1 ∈ strip W (Rgrp W (rat a.x₀)) C} =
      (fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
        Formalism.L2.Theta.mt W p.1.1⁻¹ ⬝ ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1)) ⁻¹' S := by
    ext p
    exact (hSiff p.1.1 p.2.1).symm
  rw [hpre]
  refine _root_.GlobalTheory.FourierRealPart.integral_preimage_eq_zero D ψ ha.weil.std V V₀ W ρ a.d _ (a.totMeas 𝓑) (a.tot G Φ) hint _ (measurable_point a.x₀) ?_ S hS hSinf
  intro c hc
  have h0 := hvan c hc
  rw [(_root_.GlobalTheory.Asc.unfold_family D ψ V V₀ W ρ Y a ha G _ hG (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all ha.weil.std hΦ _) 𝓑 h𝓑).2.2.1] at h0
  simpa only [tot_heisO_extY a ha G Φ hΦ c] using h0
end
end

