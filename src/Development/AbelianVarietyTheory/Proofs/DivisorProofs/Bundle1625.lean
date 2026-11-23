module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularGramInverseInertPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSchroedingerFamilyAtPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.SchrLocModel

theorem box_mem : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ] (s : (κ → Fv F v) → ℂ), s ∈ SB (κ → Fv F v) → s ≠ 0 → ∃ (x₀ : κ → Fv F v) (N₀ : ℕ), ∀ N ≥ N₀, Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - x₀ i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ) ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) :=
  GlobalTheory.T.schwartzBruhat_span_box_indicator_schrodinger

theorem decomp : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (φ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) → ∃ N₀ : ℕ, ∀ N ≥ N₀, φ ∈ Submodule.span ℂ (Set.range fun c : κ → Fv F v => Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - c i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ)) :=
  GlobalTheory.T.schwartzBruhat_mem_span_coordinateBox_indicators

def rhoSB {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) {κ : Type}
    [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) : Module.End ℂ (SB (κ → Fv F v)) where
  toFun φ := ⟨schr ψ w φ, GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ w φ φ.2⟩
  map_add' φ φ' := by
    apply Subtype.ext; funext x
    simp only [schr, Submodule.coe_add, Pi.add_apply, mul_add]
  map_smul' c φ := by
    apply Subtype.ext; funext x
    simp only [schr, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem rhoSB_apply {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ)
    {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) (φ : SB (κ → Fv F v)) :
    ((rhoSB v ψ hψ w φ : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ) = schr ψ w φ := rfl

theorem schr_mem_span {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (s : (κ → R) → ℂ) (w : (κ → R) × (κ → R)) {f : (κ → R) → ℂ}
    (hf : f ∈ Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s)) :
    schr ψ w f ∈ Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s) := by
  let L : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) :=
    { toFun := schr ψ w
      map_add' := fun a b => by funext x; simp only [schr, Pi.add_apply, mul_add]
      map_smul' := fun c a => by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hle : Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s) ≤
      (Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s)).comap L := by
    rw [Submodule.span_le]
    rintro _ ⟨w', rfl⟩
    show schr ψ w (schr ψ w' s) ∈ Submodule.span ℂ (Set.range fun w : (κ → R) × (κ → R) => schr ψ w s)
    rw [schr_schr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w + w', rfl⟩)
  exact hle hf

theorem schr_fst {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a : κ → R) (f : (κ → R) → ℂ) : schr ψ (a, 0) f = fun x => f (x + a) := by
  funext x; simp [schr]

theorem span_schr (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ)
    (hu : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F)
    (κ : Type) [Fintype κ] (s : (κ → Fv F v) → ℂ) (hs : s ∈ SB (κ → Fv F v)) (hs0 : s ≠ 0) :
    ∀ φ ∈ SB (κ → Fv F v),
      φ ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr ψ w s) := by
  intro φ hφ
  obtain ⟨x₀, N₀, hN₀⟩ := box_mem F v ψ hu κ s hs hs0
  obtain ⟨N₁, hN₁⟩ := decomp F v κ φ hφ
  refine Submodule.span_le.mpr ?_ (hN₁ (max N₀ N₁) (le_max_right _ _))
  rintro _ ⟨c, rfl⟩
  have h := schr_mem_span ψ s (x₀ - c, 0) (hN₀ (max N₀ N₁) (le_max_left _ _))
  rw [schr_fst] at h
  rw [SetLike.mem_coe]
  convert h using 1
  funext x
  have e : ∀ i, x i + (x₀ i - c i) - x₀ i = x i - c i := fun i => by ring
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.add_apply, Pi.sub_apply, e, Pi.one_apply]

end GlobalTheory.SchrLocModel

namespace GlobalTheory.SchrLocModel

theorem locCo_onto {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {Wm : Type} [AddCommGroup Wm] [Module (AF F) Wm]
    {Bf : Wm → Wm → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ) {Y : Type} [AddCommGroup Y] (Xm : Y →+ Wm)
    (hX : ∀ z : Wm, At (evFin F v) z ↔ ∃ y, Xm y = z) (w : (κ → Fv F v) × (κ → Fv F v)) :
    ∃ x, GlobalTheory.LatVac.locCo co v (Xm x) = w := by
  set p : (κ → AF F) × (κ → AF F) := (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)) with hp
  have hzat : At (evFin F v) (co.e.symm p) := by
    intro u hu
    have hp0 : u • p = 0 := by
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · exact GlobalTheory.LatVac.at_liftV v (w.1 k) u hu
      · exact GlobalTheory.LatVac.at_liftV v (w.2 k) u hu
    rw [← map_smul, hp0, map_zero]
  obtain ⟨x, hx⟩ := (hX _).1 hzat
  refine ⟨x, ?_⟩
  rw [hx]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · show evFin F v ((co.e (co.e.symm p)).1 k) = w.1 k
    rw [LinearEquiv.apply_symm_apply]
    exact GlobalTheory.LatVac.evFin_liftV v (w.1 k)
  · show evFin F v ((co.e (co.e.symm p)).2 k) = w.2 k
    rw [LinearEquiv.apply_symm_apply]
    exact GlobalTheory.LatVac.evFin_liftV v (w.2 k)

theorem exists_locRho : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ), IsStd ψ → PsiUnr ψ v →
    ∀ {Wm : Type} [AddCommGroup Wm] [Module (AF F) Wm] {Bf : Wm → Wm → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ)
      (Y : Type) [AddCommGroup Y] (Xm : Y →+ Wm) (χ : Y → Y → ℂ),
      (∀ z : Wm, At (evFin F v) z ↔ ∃ y, Xm y = z) → (∀ x y, ψ (⅟(2 : AF F) * Bf (Xm x) (Xm y)) = χ x y) →
      ∃ ρ : Y → Module.End ℂ (SB (κ → Fv F v)), ρ 0 = 1 ∧ (∀ x y, ρ x * ρ y = χ x y • ρ (x + y)) ∧
        (∀ x (φ : SB (κ → Fv F v)), Acts (evFin F v) (co.rho ψ (Xm x)) (φ : (κ → Fv F v) → ℂ)
          ((ρ x φ : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ)) ∧
        ∀ s : SB (κ → Fv F v), s ≠ 0 → Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ := by
  intro F _ _ v ψ hstd hunr Wm _ _ Bf κ _ co Y _ Xm χ hX hχ
  have hc : Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
    have h : Continuous (GlobalTheory.LatVac.liftV v) := by
      change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
      exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
    exact hstd.1.comp h
  have evFin_invOf_two : evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    have h : evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
    rwa [map_mul, map_ofNat] at h
  have hat : ∀ x, At (evFin F v) (Xm x) := fun x => (hX (Xm x)).2 ⟨x, rfl⟩
  refine ⟨fun x => rhoSB v (GlobalTheory.LatVac.psiAt ψ v) hc (GlobalTheory.LatVac.locCo co v (Xm x)), ?_, ?_, ?_, ?_⟩
  · apply LinearMap.ext; intro φ
    apply Subtype.ext; funext z
    simp [rhoSB, schr]
  · intro x y
    apply LinearMap.ext; intro φ
    apply Subtype.ext
    show schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v (Xm x))
        (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v (Xm y)) φ) =
      χ x y • schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v (Xm (x + y))) φ
    rw [schr_schr, map_add Xm, map_add (GlobalTheory.LatVac.locCo co v), ← hχ]
    congr 1
    rw [GlobalTheory.VacIndic.psi_of_at ψ (GlobalTheory.VacIndic.at_mul_left (GlobalTheory.LatVac.DualLoc.at_form co v (hat x) (Xm y))),
      map_mul (evFin F v), evFin_invOf_two, GlobalTheory.LatVac.DualLoc.evFin_form co v]
    rfl
  · intro x φ
    exact GlobalTheory.VacBridge.rho_acts_locCo co ψ v (Xm x) (hat x) φ
  · intro s hs
    rw [eq_top_iff]
    rintro t -
    have key := span_schr F v (GlobalTheory.LatVac.psiAt ψ v) (fun z => hunr z) κ s s.2
      (fun h => hs (Subtype.ext h)) t t.2
    have hmap : Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) =>
        schr (GlobalTheory.LatVac.psiAt ψ v) w (s : (κ → Fv F v) → ℂ)) =
        (Submodule.span ℂ (Set.range fun x => rhoSB v (GlobalTheory.LatVac.psiAt ψ v) hc
          (GlobalTheory.LatVac.locCo co v (Xm x)) s)).map (SB (κ → Fv F v)).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 1
      ext f
      constructor
      · rintro ⟨w, rfl⟩
        obtain ⟨x, hx⟩ := locCo_onto v co Xm hX w
        exact ⟨x, by simp only [Function.comp_apply, Submodule.subtype_apply, rhoSB_apply, hx]⟩
      · rintro ⟨x, rfl⟩
        exact ⟨_, rfl⟩
    rw [hmap] at key
    obtain ⟨u, hu, hut⟩ := key
    rwa [show u = t from Subtype.ext hut] at hu

end GlobalTheory.SchrLocModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTupleDataGivenLevelCoeffMaps
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinnedDataGiven

theorem latEmb_iotaW {D : D7} (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) : LatEmb (Wc D i) (iotaW T i) := by
  have key : ∀ (V : HSp D) (_ : T.V ((i : ℕ) + 1) T.toCore.σ₀ = V) (hr : V.rank = D.R.r),
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) := by
    rintro V rfl hr
    obtain ⟨_, -, -, -, -, -, -, hemb, -⟩ := hT.adPin _ (inR i) _ T.toCore.good_σ₀
    exact hemb
  exact key _ (hT.spaceW _ (inR i) _ T.toCore.good_σ₀) (rank_Wc i)


set_option maxHeartbeats 2000000 in
theorem exists_pins_given : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → R.thP_vP → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → Finite T0 → QGuard R → ∀ i : Fin D.R.m, VStd D i → ∀ (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La), LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → ∀ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧ O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧ O'.lev = lev ∧ CoefficientBaseChange R i O'.jL (inC O'.c') (c0L i) O'.c0' := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hchi hfam hmodels hvP hfw hpb hfin hG i hV lev hlev gramR c0R c0L htie
  obtain ⟨fw⟩ := id hfw
  have hT := fw.laws
  obtain ⟨pd, l₂, c₁, h1, h2, hc⟩ := GlobalTheory.TupleCover.exists_covers T R hT hL hpb hG i (Vc D i).rank
  choose Mφ hMφ hφ using fun t => GlobalTheory.T.exists_level_place_datum_over_number_field D G Pl0 T0 A _ R hL hvP i hV t _ (iotaW T i) (latEmb_iotaW T hT i)
  choose MB hMB hB using fun t => _root_.GlobalTheory.Mem.BVal.exists_field_BIs D G Pl0 T0 A _ R hL i t
  have := c₁.fin
  obtain ⟨c', hc'⟩ := GlobalTheory.TupleCover.exists_coeff_ge T.Q.l (c₁.F ⊔ ⨆ t, (Mφ t ⊔ MB t))
  have h3 : c₁.F ≤ c'.F := le_sup_left.trans hc'
  have h4 : ∀ t, Mφ t ⊔ MB t ≤ c'.F := fun t => ((le_iSup (fun t => Mφ t ⊔ MB t) t).trans le_sup_right).trans hc'
  have hle : T.Q.c.F ≤ c'.F := h1.trans h3
  have hLL := h2.trans h3
  obtain ⟨dδ, U₂, dict₂, xi, -, hcov, hhalf, hxi, hcxi, hmod, -⟩ := hc c' hle h3
  let jL : D.what₂.LL →+* c'.F := D.what₂.embLL.codRestrict c'.F fun x => hLL ⟨x, rfl⟩
  have hjL : (inC c').comp jL = D.what₂.embLL := RingHom.ext fun _ => rfl
  obtain ⟨c0', hc0, hplace⟩ := _root_.GlobalTheory.Div.CoefExtension.exists_ext_placeEx D G Pl0 T0 A _ R hL hchi hfam hmodels gramR c0R c0L htie i c'.F jL (inC c') hjL
  obtain ⟨Cl, fCl, h, J', bad, Lh, gam, vol, La, Nc, hrep, hbad, hcl⟩ :=
    GlobalTheory.SplitReps.exists_repsR_repsCov R i (hL.βV i) hV c'.F (T.Q.Xo ((i : ℕ) + 1)) c' id dδ
  choose B hBis using fun t => hB t c'.F (le_sup_right.trans (h4 t)) (bad t) (hbad t).2.2.2.2
    fun PP hPP => (hrep t).1.2.1 PP (Or.inr hPP)
  have hodd : Odd ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) := by
    obtain ⟨e1, e2, -⟩ := hT.pins.2.2.2 _ (inR i)
    have h5 := Formalism.L2.NTheta.odd_r D.R
    have h6 := i.2
    have h7 := D.R.m_add_three_le_k
    rw [e1, e2]
    convert h5 using 1
    simp only [Ranks.sigW, Ranks.r]
    omega
  choose epF hepF using fun t => (GlobalTheory.ClassTieCompare.exists_epIs_iff (n := (Vc D i).rank) (Dw := T.Q.Dw ((i : ℕ) + 1))
    (bad t) (B t)).2 fun L cc g d => _root_.GlobalTheory.LawOfSquares.law_of_squares _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  obtain ⟨io, hw, hio⟩ := _root_.GlobalTheory.CoefMapRecord.exists_io_record D T.Q hT.pins κ fw.kap i c'
  choose φ hφis using fun t => hφ t c'.F (le_sup_left.trans (h4 t)) (hhalf t).2.2 (Mfr (dδ t).l₂) fun PP hPP c hc => by
    have hM : (dδ t).l₂.Mb ≤ PP.asIdeal := by
      rw [(hcov t).1.2.2.2.1]
      rcases hPP with hPP | hPP
      · rw [(hhalf t).1]
        exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
      · exact Ideal.mul_le_right.trans ((hhalf t).2.1 PP hPP)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ T.Q.H.bar.surjective).1 hc
    refine ⟨b, hM hb, ?_⟩
    change _ = star ((T.Q.H.bar b : 𝓞 D.host.E) : D.host.E)
    rw [T.Q.H.bar_eq]
    exact (star_star _).symm
  choose thAd hth using fun t => _root_.GlobalTheory.AdelicSide.exists_thAd_of_models D G Pl0 T0 A _ R hmodels i t _ _ c0' _ (h t) _ (hrep t).1.2.2.1
    (hrep t).1.2.2.2.2.2.1 (v₀ i (sg0 D A))
  have hact := fun c => GlobalTheory.T.levelAction_framedPoints_isAction D G Pl0 T0 A T R hL hT hpb i c lev hlev
  refine ⟨{ c' := c', hle := hle, jL := jL, hV := hT.spaceW _ (inR i) _ rfl, c0' := c0', lev := lev, dδ := dδ, Cl' := Cl,
            bad := bad, Lh := Lh, La := La, Nc := Nc, gam := gam, vol := vol, ep := fun t k => epF t (Lh t k), B := B,
            epF := epF, io := io, hw := hw, φ := φ,
            w := fun t _ q => (dδ t).eF.symm (phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q),
            U₂ := U₂, dict₂ := dict₂, xi := xi, thAd := thAd,
            Plc := fun t x => ∃ x₀, Place R i t (h t) c0' (jVx R i t x₀) x }, hLL,
    ⟨⟨hjL, hV, fw.hv₀ i _, ⟨gramR, c0R, c0L, htie, hc0⟩, hlev⟩,
    fun t => ⟨⟨h t, J' t, (hrep t).1, hplace t _ _, hth t, fun _ => Iff.rfl⟩, hBis t, hxi t, hφis t, hhalf t⟩,
    ⟨hact _, hact _⟩,
    hbad, hcl, fun t => ⟨fun _ => rfl, hepF t⟩, hio, fun t k q => AlgEquiv.apply_symm_apply _ _, hcov, hcxi, hmod⟩, rfl, hc0⟩

end GlobalTheory.PinnedDataGiven
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameCoordsOfMemTorusLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaLawLat

variable {D : D7}

theorem entry_mem_AA {N N' : ℕ} {z : Matrix (Fin N') (Fin N) D.host.E}
    (hz : z ∈ GlobalTheory.InertSign.RL D D.host.ccK (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N'))
    (p : Fin N') (q : Fin N) : z p q ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hz
    have hAint : GlobalTheory.InertSign.IntE D (A p q) := by
      have h1 : (Pi.single q 1 : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
        refine GlobalTheory.ThetaLatImage.mem_stdL.2 fun i => ?_
        by_cases h : i = q
        · subst h; rw [Pi.single_eq_same]; exact one_mem _
        · rw [Pi.single_eq_of_ne h]; exact zero_mem _
      have h2 := GlobalTheory.ThetaLatImage.mem_homL.1 hA _ h1
      rw [Matrix.mulVec_single_one] at h2
      exact GlobalTheory.ThetaLatImage.mem_stdL.1 h2 p
    obtain ⟨o, ho⟩ := hAint
    have ht' : t ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := by
      induction ht using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨c, hc, a, ha, rfl⟩ := ht
        have hc' : ((c : D.host.K) : D.host.E) ∈ (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
          FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) hc)
        exact FractionalIdeal.mul_mem_mul hc' ha
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | smul o x _ hx => exact Submodule.smul_mem _ o hx
    rw [Matrix.smul_apply, smul_eq_mul, ← ho, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o ht'
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul o x _ hx => exact Submodule.smul_mem _ o hx

end GlobalTheory.ThetaLawLat

namespace GlobalTheory.ThetaLawLat

variable {D : D7}

theorem one_mem_intAf' : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem inv_frame {S : HSp D} (frS : GL (Fin S.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1) :
    (frS⁻¹).1 = frS.1ᴴ * S.gram := by
  have h1 : (frS.1ᴴ * S.gram) * frS.1 = 1 := hS
  calc (frS⁻¹).1 = ((frS.1ᴴ * S.gram) * frS.1) * (frS⁻¹).1 := by rw [h1, Matrix.one_mul]
    _ = frS.1ᴴ * S.gram := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem finRat_frame_mem_latO {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (hz : ∀ p q, z p q ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)) :
    GlobalTheory.VacUnique.finRat S T (frT.1 * z * (frS⁻¹).1) ∈
      latO S T (colLat frS : Set (Fin S.rank → D.host.E)) (colLat frT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  have key : GlobalTheory.VacUnique.finRat S T (frT.1 * z * (frS⁻¹).1) =
      ∑ p, ∑ q, Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F]
        (z p q * (fun a => frT.1 a p) i * ∑ k, star ((fun a => frS.1 a q) k) * S.gram k j) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.of_apply]
    simp only [← TensorProduct.tmul_sum]
    show (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (frT.1 * z * (frS⁻¹).1) i j = _
    congr 1
    rw [inv_frame frS hS]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [key]
  refine AddSubgroup.sum_mem _ fun p _ => AddSubgroup.sum_mem _ fun q _ => AddSubgroup.subset_closure ?_
  exact ⟨1, one_mem_intAf', fun v h => (h trivial).elim, z p q, hz p q, _,
    Submodule.subset_span ⟨q, rfl⟩, _, Submodule.subset_span ⟨p, rfl⟩, rfl⟩

theorem mem_La_frame : ∀ {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank), ∃ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T v ∈ latO S T (colLat frS : Set (Fin S.rank → D.host.E)) (colLat frT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ x = δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b) := by
  intro D S T frS frT hS hT δ x hx
  obtain ⟨z, hz, rfl⟩ := GlobalTheory.ThetaLatImage.La_sub hx
  refine ⟨frT.1 * z * (frS⁻¹).1, finRat_frame_mem_latO frS frT hS z (GlobalTheory.ThetaLawLat.entry_mem_AA hz), ?_⟩
  have hmap : ∀ τ, Matrix.of (GlobalTheory.VacUnique.infRat S T (frT.1 * z * (frS⁻¹).1) τ) =
      GlobalTheory.FockPos.frAt frT τ * Matrix.of (fun i j => tauE D τ (z i j)) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ := by
    intro τ
    have hi : (GlobalTheory.FockPos.frAt frS τ)⁻¹ = (frS⁻¹).1.map (tauE D τ) := by
      refine Matrix.inv_eq_right_inv ?_
      rw [GlobalTheory.FockPos.frAt, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hi]
    show (frT.1 * z * (frS⁻¹).1).map (tauE D τ) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  funext τ a b
  rw [GlobalTheory.ThetaLatImage.pt_apply]
  show _ = δ * ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T (frT.1 * z * (frS⁻¹).1) τ) *
    GlobalTheory.FockPos.frAt frS τ) a b
  rw [hmap τ, GlobalTheory.ThetaLawOF.coord_back frS frT (fun τ i j => tauE D τ (z i j)) τ]
  rfl

end GlobalTheory.ThetaLawLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRosatiCoordinatesDivisibleOfPow
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section
namespace GlobalTheory.FlatCM.RosatiCoord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {σ₁ : K →+* ℂ} {A B : PAT H (Sp (𝓞 K))}

theorem weilEq_prod_snd {I₀ : Type} (f : A.t.G ⟶ B.t.G) (hf : IsMonHom f)
    (G : I₀ → (A.t.G ⟶ B.t.G)) (hG : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (G i)) (r : I₀ → 𝓞 E)
    (h : ∀ i, WeilEq B.t.PP.L f (G i) A.t.PP.L (A.t.act.act (r i)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {T : Finset I₀} (hT : T.Nonempty) :
    WeilEq B.t.PP.L f (∏ i ∈ T, G i) A.t.PP.L (A.t.act.act (∑ i ∈ T, r i)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h a
  | cons a s has hs ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    have hs' : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (∏ i ∈ s, G i) :=
      Finset.prod_induction _ (GlobalTheory.Serre.IsLinearHom A.t.act B.t.act) (fun f g hf hg => hf.mul hg)
        (GlobalTheory.Serre.IsLinearHom.one _ _) fun i _ => hG i
    exact _root_.GlobalTheory.weilEq_mul_right_add E H K σ₁ A B f (G a) _ hf (hG a).isMonHom hs'.isMonHom _ _ (h a) ih

theorem exists_mul_eq_gram_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin q) (Fin q) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (n : ℕ) (x : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G), 0 < n →
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ n = ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ a, ∃ y : 𝓞 E, (n : 𝓞 E) * y = ∑ b, gP a b * H.bar (x b) := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p q X gP gQ hG n x f hn hf hfx a
  have hφ : ∀ b, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act (phiP X b) := fun b => X.lin (Sum.inl b)
  obtain ⟨r, hr⟩ := GlobalTheory.FlatCM.GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP
    (phiP X a) f (hφ a) hf
  have h1 := weilEq_prod_snd (phiP X a) (hφ a).isMonHom (fun _ : ℕ => f) (fun _ => hf) (fun _ => r) (fun _ => hr)
    (Finset.nonempty_range_iff.2 hn.ne')
  rw [Finset.prod_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hfx] at h1
  have h2 := weilEq_prod_snd (phiP X a) (hφ a).isMonHom (fun b => (X.A true).t.act.act (x b) ≫ phiP X b)
    (fun b => (GlobalTheory.Serre.IsLinearHom.act _ _).comp (hφ b)) (fun b => gP a b * H.bar (x b))
    (fun b => _root_.GlobalTheory.CM.ActRight.weilEq_act_right E H K σ₁ (X.A true) X.B _ _ (hφ a).isMonHom (hφ b).isMonHom _ (x b) (hG.1 a b))
    (T := Finset.univ) ⟨a, Finset.mem_univ a⟩
  exact ⟨r, _root_.GlobalTheory.TwistScalarUnique.eq_of_weilEq E H K ρ σ₁ (X.A true) X.ρ_sq X.typeP _ _ fun k u v e hk hu hv =>
    (h1 k u v e hk hu hv).symm.trans (h2 k u v e hk hu hv)⟩

end GlobalTheory.FlatCM.RosatiCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularGramInverseInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unimodular_gram_inverse_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (n r s : ℕ) (X : Spc F E n), X.IsHerm σ B r s →
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Formalism.UG.IsUnramInv ϖ σL q → Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ P : GL (Fin n) L, (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) →
      ∃ JS : GL (Fin n) L, JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧
        ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = GlobalTheory.InertLocFrame.gram σL ι P X.J ∧
        ∀ i j, σL ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i := by
  first | exact @GlobalTheory.InertGram.exists_gram_inv | exact GlobalTheory.InertGram.exists_gram_inv | (intros; apply GlobalTheory.InertGram.exists_gram_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlaceStatement
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergLattice_selfDual_every_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) z →
      (z ∈ latAtV X W v ↔ ∀ γ ∈ latAtV X W v, B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) z γ) = 1) := by
  first | exact @GlobalTheory.LatSelfDualAll.latAtV_selfDual | exact GlobalTheory.LatSelfDualAll.latAtV_selfDual | (intros; apply GlobalTheory.LatSelfDualAll.latAtV_selfDual <;> assumption)
end

