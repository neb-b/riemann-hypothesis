module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1683
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0801
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0106
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankAtPlacesFromComparison
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.TraceClassRank

section General

open scoped TensorProduct

attribute [local instance 2000] Submodule.module

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem goodOp_rho_comm {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (j : Fin D.R.m) (g : G) (x : Fin (R.nW j) → D.what₂.LL) :
    OntoChain.goodOp R j ((R.FW j).ρ g x) = (R.FW j).ρ g (OntoChain.goodOp R j x) := by
  have h := LinearMap.congr_fun (goodOp_comm (R := R) hX j g) x
  simp only [LinearMap.comp_apply, twRep_apply, map_smul] at h
  have h' := congrArg (fun y => (((R.FW j).chi g : D.what₂.LLˣ) : D.what₂.LL) • y) h
  simp only [smul_smul, Units.mul_inv, one_smul] at h'
  exact h'

variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (OnTies.srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}

theorem tie_e_comm_rho (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (ha : ActionPin h fw ι ℓ)
    (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (g : P) : O.e i ∘ₗ O.ρ i g = O.ρ i g ∘ₗ O.e i := by
  refine LinearMap.ext fun x => (toForms_bijective h fw ι z).1 ?_
  simp only [LinearMap.comp_apply]
  rw [t.e_eOp, t.rho_eq_of_actionPin ha, t.rho_eq_of_actionPin ha, t.e_eOp]
  exact goodOp_rho_comm hX ι (inc g) _

theorem tie_thetaJ (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (ha : ActionPin h fw ι ℓ)
    (hi : Function.Injective inc) (hU : U ≤ inc.range) (hd : FormsDetermined R ι) (hM : SpanOverClasses R ι U ψ ph v p)
    (hty : ∀ x ∈ thetaBase R ι U ψ ph v p, ∀ u : U, (R.FW ι).ρ u x = ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • x)
    {n : ℕ} (hp : RunPin R ι n v p) (hA : CompareOffOwn h fw ι ℓ U ψ ph v p) :
    (O.ThJ v i).FG ∧ O.ThJ v i ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ i) O.U O.ψ).restrictScalars (𝓞 D.what₂.LL) ∧
      Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v i) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v i) := by
  have hb := toForms_bijective h fw ι z
  refine ⟨?_, fun x hx => ?_, trace_lattice_le_theta_lattice_at_place t hi hU hp hA⟩
  · refine Submodule.fg_of_fg_map_injective ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) hb.1 ?_
    rw [t.ThJ_eq, Submodule.map_comap_eq_of_surjective (f := (toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) hb.2]
    exact thetaBase_fg hd hM
  · rw [t.ThJ_eq] at hx
    have hx' : toForms h fw ι z x ∈ thetaBase R ι U ψ ph v p := hx
    change x ∈ Formalism.EigenvalueLevelCeiling.eig _ _ _
    unfold Formalism.EigenvalueLevelCeiling.eig
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero]
    intro u
    have hU' : ∀ g : P, g ∈ O.U → inc g ∈ U := fun g hg => by
      rw [t.U_eq] at hg
      exact hg
    have hu : inc u ∈ U := hU' u u.2
    apply hb.1
    rw [t.rho_eq_of_actionPin ha, hty _ hx' ⟨inc u, hu⟩, map_smul, t.ψ_eq u hu]

end General

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}

theorem conjPl_mem_twPl (hC : (R2 p).Char (F2 p)) {w : HeightOneSpectrum (𝓞 D.what₂.LL)} (hw : w ∈ p.R.twPl) :
    Formalism.DivisionValues.conjPl w ∈ p.R.twPl := by
  by_contra h
  exact hC.tup.mu_ne w hw ((hC.tup.mu_conj w).symm.trans (hC.tup.mu_off _ h))

end Point

end GlobalTheory.BigOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPolynomialVectorReachedByRealDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigNZ.DatReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

section Tens

variable (W : G.Weil) {X Y : Node} {p : Path T X Y}

theorem tensT_zero (τ : TotT G p) : tensT W (0 : PolT G p →₀ ℂ) τ = 0 := Finsupp.sum_zero_index

theorem tensT_add (a b : PolT G p →₀ ℂ) (τ : TotT G p) : tensT W (a + b) τ = tensT W a τ + tensT W b τ := by
  unfold tensT
  refine Finsupp.sum_add_index' (fun P => by simp) (fun P c₁ c₂ => ?_)
  simp only [add_mul, Finsupp.single_add, Finsupp.sum_add]

theorem tensT_smul (c : ℂ) (a : PolT G p →₀ ℂ) (τ : TotT G p) : tensT W (c • a) τ = c • tensT W a τ := by
  unfold tensT
  rw [Finsupp.sum_smul_index' (fun P => by simp), Finsupp.smul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  dsimp only
  rw [Finsupp.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  dsimp only
  rw [Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_assoc]

theorem fock_one (q : Pair T) (f : WO (G.pS q) (G.pT q) → ℂ) : W.fock q f 1 = f := by
  unfold GridData.Weil.fock pureTensorO pureTensorL
  rw [show (1 : MvPolynomial (FVar D (G.pT q).rank (G.pS q).rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 by
    rw [MvPolynomial.coe_basisMonomials]; rfl, Module.Basis.constr_basis]
  simp [opPow]

end Tens

section Datum

variable {t : T} {i j : ℕ} (W : G.Weil) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)

noncomputable def onePol : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) := (((), 1), 1)

theorem tensT_one (τ : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)) : tensT W (Finsupp.single onePol 1) τ = τ := by
  unfold tensT
  rw [Finsupp.sum_single_index (by simp)]
  have hz : ∀ d : PureT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j), Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d onePol = d := by
    rintro ⟨⟨⟨⟩, d₁⟩, d₂⟩
    show (((), W.fock _ d₁ 1), W.fock _ d₂ 1) = (((), d₁), d₂)
    rw [fock_one, fock_one]
  simp only [hz, one_mul]
  exact Finsupp.sum_single τ

theorem isDatumA_zero : IsDatumA W e Γ (0 : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)) 0 := by
  refine ⟨Submodule.zero_mem _, fun u => ?_⟩
  have : Γ.M.co.rho W.ψ u 0 = 0 := by
    funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
  rw [this, Finsupp.sum_zero_index]
  simp [GlobalTheory.WeilM.thetaSum]

theorem datumA_add (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ) {τ τ' : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)} {Φ Φ'} (h : IsDatumA W e Γ τ Φ)
    (h' : IsDatumA W e Γ τ' Φ') : IsDatumA W e Γ (τ + τ') (Φ + Φ') := by
  refine ⟨add_mem h.1 h'.1, fun u => ?_⟩
  have e1 : Γ.M.co.rho W.ψ u (Φ + Φ') = Γ.M.co.rho W.ψ u Φ + Γ.M.co.rho W.ψ u Φ' := by
    funext x; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply]; ring
  rw [e1, GlobalTheory.WeilM.thetaSum_add _ (GlobalTheory.HeisSchA.rho_mem_schA _ _ hψ _ _ h.1) (GlobalTheory.HeisSchA.rho_mem_schA _ _ hψ _ _ h'.1),
    h.2, h'.2, Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

theorem datumA_smul (c : ℂ) {τ : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)} {Φ} (h : IsDatumA W e Γ τ Φ) :
    IsDatumA W e Γ (c • τ) (c • Φ) := by
  refine ⟨Submodule.smul_mem _ c h.1, fun u => ?_⟩
  have e1 : Γ.M.co.rho W.ψ u (c • Φ) = c • Γ.M.co.rho W.ψ u Φ := by
    funext x; simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]; ring
  rw [e1, GlobalTheory.WeilM.thetaSum_smul, h.2, Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  simp only [smul_eq_mul, mul_assoc]

end Datum

section Pure

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)

theorem pure_zero : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : SInf F κ) φ = 0 := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]

theorem pure_add (f f' : SInf F κ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + f') φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_smul (c : ℂ) (f : SInf F κ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end Pure

theorem datum_real : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ n Φ τ τ', HasFlip B t ρ i j n Φ τ τ' →
    ∀ φ, IsFinPart Γ.M X.T φ → ∀ f₀, f₀ ≠ 0 → Γ.M.IsGauss Bs.ψ Bs.emb f₀ → IsDatumA W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∃ a, IsDatumA W e Γ (tensT W a τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  intro D T L sc G μ₀ hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF φ hφ f₀ hf₀ hG hD
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  change TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) at τ
  let N : Submodule ℂ (SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank))) :=
    { carrier := {f | ∃ a, IsDatumA W e Γ (tensT W a τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)}
      zero_mem' := ⟨0, by rw [tensT_zero, pure_zero]; exact isDatumA_zero W e Γ⟩
      add_mem' := by
        rintro f f' ⟨a, ha⟩ ⟨a', ha'⟩
        exact ⟨a + a', by rw [tensT_add, pure_add]; exact datumA_add W e Γ hψ ha ha'⟩
      smul_mem' := by
        rintro c f ⟨a, ha⟩
        exact ⟨c • a, by rw [tensT_smul, pure_smul]; exact datumA_smul W e Γ c ha⟩ }
  have h0 : f₀ ∈ N := ⟨Finsupp.single onePol 1, by rw [tensT_one]; exact hD⟩
  have hle : Γ.M.Pol Bs.ψ Bs.emb ≤ N := sInf_le ⟨fun g hg => by
      obtain ⟨c, rfl⟩ := _root_.GlobalTheory.GaussLine.gauss_eq_smul Bs Γ X om om' hT f₀ hf₀ hG g hg
      exact N.smul_mem c h0,
    fun u hu f ⟨a, ha⟩ f₁ h1 => _root_.GlobalTheory.BigNZ.DatRealStable.datum_stable hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF φ hφ f a ha u hu f₁ h1⟩
  exact fun f hf => hle hf

end GlobalTheory.BigNZ.DatReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealizationEmbeddingCompatible
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BigOn.Exp

section Generic

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}

def readExt (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
    (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c)) : L ⊗[O] M →+ (G → ℂ) :=
  TensorProduct.liftAddHom
    { toFun := fun b => (DistribSMul.toAddMonoidHom _ (eL b)).comp rd.toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    fun c b f => by
      change eL (c • b) • rd f = eL b • rd (c • f)
      rw [← algebraMap_smul (FractionRing O) c f, LinearMap.map_smulₛₗ rd, Algebra.smul_def c b, map_mul, hL, smul_smul, mul_comm]

variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))

theorem readExt_tmul (b : L) (f : M) : readExt rd eL hL (b ⊗ₜ f) = eL b • rd f := rfl

theorem readExt_smul (b : L) (x : L ⊗[O] M) : readExt rd eL hL (b • x) = eL b • readExt rd eL hL x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | tmul a f =>
    rw [TensorProduct.smul_tmul', readExt_tmul, readExt_tmul, smul_eq_mul, map_mul, mul_smul]

theorem readExt_injective
    (hF : ∀ (n : ℕ) (v : Fin n → M), LinearIndependent (FractionRing O) v → LinearIndependent ℂ fun c => rd (v c)) :
    Function.Injective (readExt rd eL hL) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  let v := Module.finBasis (FractionRing O) M
  have key : ∀ x : L ⊗[O] M, ∃ d : O, d ≠ 0 ∧ ∃ c : _ → L, d • x = ∑ a, c a ⊗ₜ v a := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | add x y hx hy =>
      obtain ⟨d, hd, c, e⟩ := hx
      obtain ⟨d', hd', c', e'⟩ := hy
      refine ⟨d * d', mul_ne_zero hd hd', d' • c + d • c', ?_⟩
      rw [smul_add, mul_smul d d' y, mul_comm, mul_smul, e, e']
      simp [Finset.smul_sum, TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.smul_tmul']
    | tmul a f =>
      obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fun c => v.repr f c
      choose y hy using hd
      refine ⟨d, nonZeroDivisors.coe_ne_zero d, fun c => y c • a, ?_⟩
      rw [← TensorProduct.tmul_smul]
      conv_lhs => rw [← v.sum_repr f]
      rw [Finset.smul_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing O) (y c), hy, smul_assoc]
  obtain ⟨d, hd, c, e⟩ := key x
  have h1 : ∑ a, eL (c a) • rd (v a) = 0 := by
    have := congrArg (readExt rd eL hL) e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← algebraMap_smul L d x, readExt_smul, hx, smul_zero, map_sum] at this
    exact this.symm
  have h2 : ∀ a, c a = 0 := fun a => eL.injective
    ((Fintype.linearIndependent_iff.1 (hF _ v v.linearIndependent) _ h1 a).trans (map_zero _).symm)
  have h3 : d • x = 0 := by simp [e, h2]
  have h4 : ∀ x : L ⊗[O] M,
      LinearMap.lTensor L (((algebraMap O (FractionRing O) d)⁻¹ • LinearMap.id :
        Module.End (FractionRing O) M).restrictScalars O) (d • x) = x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy]
    | tmul a f =>
      rw [← TensorProduct.tmul_smul, LinearMap.lTensor_tmul]
      congr 1
      change (algebraMap O (FractionRing O) d)⁻¹ • d • f = f
      rw [← algebraMap_smul (FractionRing O) d f, inv_smul_smul₀ (by simpa using hd)]
  rw [← h4 x, h3, map_zero]

end Generic


end GlobalTheory.BigOn.Exp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorArchimedeanMemAdelicSchwartz
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Words

theorem schr_archPair_mem_schA : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F h) φ ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ _ κ _ ψ hψ h φ hφ
  obtain ⟨ℓ, -, hℓ⟩ := hψ
  obtain ⟨n, f, g, hg, rfl⟩ := schA_exists_sum F hφ
  let M : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F :=
    ∑ k, (LinearMap.mulRight ℝ (h.2 k)).comp (LinearMap.proj k)
  let L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (ℓ.comp M)
  have hL : ∀ X, L X = ℓ (∑ k, X k * h.2 k) := by
    intro X
    simp [L, M]
  set c : ℝ := ℓ (∑ k, h.1 k * h.2 k) / 2 with hc
  have hgr := GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase L (-c) (-1)
  rw [← GlobalTheory.LinPhaseSeminorm.phase_eq] at hgr
  rw [schr_sum']
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span
    ⟨SchwartzMap.smulLeftCLM ℂ
      (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((-1 * L x + (-1) ^ 2 * -c : ℝ) : ℂ)))
      (SchwartzMap.compSubConstCLM ℂ (-h.1) (f i)), g i, hg i, ?_⟩
  funext a
  rw [← adeleJoin_archPart F a, schr_archPair_adeleJoin F ψ ℓ hℓ, GlobalTheory.WeilCont.pureA_adeleJoin,
    GlobalTheory.WeilCont.pureA_adeleJoin, SchwartzMap.smulLeftCLM_apply_apply hgr, SchwartzMap.compSubConstCLM_apply,
    sub_neg_eq_add, smul_eq_mul, hL, ← mul_assoc]
  congr 2
  rw [hc]
  push_cast
  ring_nf

end GlobalTheory.WeilL2Words

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftRowFiresOfWeakCharacterisation
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem thetaLiftRow_fires_of_weakCharacterisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → A3.A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R.toRealDat) (hinj : ∀ i t, Function.Injective (R.toRealDat.extV i t)) (IL : RecTie.LiftIds (RecTie.toLiftReal R.toRealDat F.lv2 tupT hm hTop hinj)), RecTie.ThetaFireRow (RecTie.toLiftReal R.toRealDat F.lv2 tupT hm hTop hinj) IL := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hC e hv tupT hm hTop hinj IL
  exact _root_.GlobalTheory.ThetaFireAssembly.thetaFireRow_toLiftReal R.toRealDat F.lv2 tupT hm hTop hinj hC.base e hv IL

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_factorizable_restriction : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl (F := F))) (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w, w ∉ S → φ w = G.M'.vac w) →
    ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')),
    (∀ w, w ∉ S → ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ,
      G.M'.co.rho B.ψ γ (pure f φ) = c • pure f φ → G.M'.co.rho B.ψ γ Ψ = c • Ψ) →
    ∃ (m : ℕ) (f' : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ' : Fin m → ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ i w, φ' i w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧ (∀ i w, w ∉ S → φ' i w = G.M'.vac w) ∧
      Ψ = ∑ i, pure (f' i) (φ' i) := by
  first | exact @GlobalTheory.VacFactor.factor | exact GlobalTheory.VacFactor.factor | (intros; apply GlobalTheory.VacFactor.factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsMulMemAddWeight
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.CuspEmb

theorem twoLevels_mul_mem_SS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la mu : Wt M.Ψ r) (F G : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → G ∈ M.SS mu → F * G ∈ M.SS (la + mu) := by
  intro E _ _ _ r U C _ _ M la mu F G hF hG c
  have hP := hF c
  have hQ := (hG c).1
  have h := ReciprocityTheory.ChartRestriction.G.AR.Up.ss_mul_pow (M.comp c).toData hP hQ 1
  have hw : castWt (M.comp_Ψ c) (la + mu) =
      castWt (M.comp_Ψ c) la + 1 • castWt (M.comp_Ψ c) mu := by
    rw [one_smul]; funext τ; rfl
  rw [hw]
  rw [pow_one] at h
  exact h

end GlobalTheory.CuspEmb
end

