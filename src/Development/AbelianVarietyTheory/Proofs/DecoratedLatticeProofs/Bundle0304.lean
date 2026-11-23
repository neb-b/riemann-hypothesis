module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlaceStabilizerPartialProductsFiniteSet
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0103
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumSplitPlaceReadsThetaClassically
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0290
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0107

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology

namespace GlobalTheory.StabSetFix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stab_fix_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop), (∀ v, P v → Tame D v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT v) → ∀ f, Vac ψ S T LS LT P f → ∀ κ κ', InK S LS P κ → InK T LT P κ' → om (κ, κ') f = f := by
  intro D ψ S T χS χT om hW LS LT hS hT P hP f hf κ κ' hκ hκ'
  have hloc := ((_root_.GlobalTheory.VacLoc.vac_loc D ψ S T χS χT om hW LS LT hS hT P (fun v hv => (hP v hv).1) f).1.1 hf)
  have one_inK : ∀ (V : HSp D) (L : Lat V) (v : Pl D), InK V L (· = v) 1 := by
    intro V L v
    refine ⟨one_mem _, fun y _ => ?_⟩
    have h1 : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
    rw [h1, Matrix.one_mulVec]
  have single : ∀ v, P v → ∀ y y', InK S LS (· = v) y → InK T LT (· = v) y' → om (y, y') f = f :=
    fun v hv y y' hy hy' => GlobalTheory.VacStabFixed.vacFixedAt D v ψ S T χS χT om hW (hP v hv).2.1 (hP v hv).2.2 LS LT hS hT f
      hloc.1 (hloc.2 v hv).2 y y' (GlobalTheory.T.inLatticeStabilizerAtPlace_of_supportedStabilizer D S LS v y hS hy) (GlobalTheory.T.inLatticeStabilizerAtPlace_of_supportedStabilizer D T LT v y' hT hy')
  have listS : ∀ l : List (GA D S), (∀ y ∈ l, ∃ v, P v ∧ InK S LS (· = v) y) → om (l.prod, 1) f = f := by
    intro l
    induction l with
    | nil => intro _; rw [List.prod_nil, Prod.mk_one_one, map_one, Module.End.one_apply]
    | cons y l ih =>
      intro h
      obtain ⟨v, hv, hy⟩ := h y (List.mem_cons_self ..)
      have e : ((y * l.prod, (1 : GA D T)) : GA D S × GA D T) = (y, 1) * (l.prod, 1) := by simp
      rw [List.prod_cons, e, map_mul, Module.End.mul_apply, ih (fun z hz => h z (List.mem_cons_of_mem _ hz)),
        single v hv y 1 hy (one_inK T LT v)]
  have listT : ∀ l : List (GA D T), (∀ y ∈ l, ∃ v, P v ∧ InK T LT (· = v) y) → om (1, l.prod) f = f := by
    intro l
    induction l with
    | nil => intro _; rw [List.prod_nil, Prod.mk_one_one, map_one, Module.End.one_apply]
    | cons y l ih =>
      intro h
      obtain ⟨v, hv, hy⟩ := h y (List.mem_cons_self ..)
      have e : (((1 : GA D S), y * l.prod) : GA D S × GA D T) = (1, y) * (1, l.prod) := by simp
      rw [List.prod_cons, e, map_mul, Module.End.mul_apply, ih (fun z hz => h z (List.mem_cons_of_mem _ hz)),
        single v hv 1 y (one_inK S LS v) hy]
  choose lS hlS hiS hinS houtS using _root_.GlobalTheory.PlaceProducts.finite_place_products D S LS P κ hS hκ
  choose lT hlT hiT hinT houtT using _root_.GlobalTheory.PlaceProducts.finite_place_products D T LT P κ' hT hκ'
  have tS := GlobalTheory.T.tendsto_unitaryAdelicPoints_agree_on_growing_finset D S κ (fun Fs => (lS Fs).prod) hiS hinS houtS
  have tT := GlobalTheory.T.tendsto_unitaryAdelicPoints_agree_on_growing_finset D T κ' (fun Fs => (lT Fs).prod) hiT hinT houtT
  funext w
  have hc := ((hW.om_cont f hloc.1 w).tendsto (κ, κ')).comp (tS.prodMk_nhds tT)
  have heq : ∀ Fs, f w = ((fun p : GA D S × GA D T => om p f w) ∘ fun Fs => ((lS Fs).prod, (lT Fs).prod)) Fs := by
    intro Fs
    have e : (((lS Fs).prod, (lT Fs).prod) : GA D S × GA D T) = ((lS Fs).prod, 1) * (1, (lT Fs).prod) := by simp
    simp only [Function.comp_apply]
    rw [e, map_mul, Module.End.mul_apply, listT _ (hlT Fs), listS _ (hlS Fs)]
  exact tendsto_nhds_unique hc (tendsto_const_nhds.congr heq)

end GlobalTheory.StabSetFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlacePairMovesLatticeVacuumReading
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.SplitGen

variable {D : D7}

theorem xiN_smul (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ)
    (c : ℂ) (f : WO S T → ℂ) : xiN θ S T hS hT δ sc (c • f) = c • xiN θ S T hS hT δ sc f := by
  funext z
  simp only [xiN, Pi.smul_apply, smul_eq_mul]
  ring

theorem xiN_sum (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ)
    {ι : Type} (s : Finset ι) (F : ι → WO S T → ℂ) :
    xiN θ S T hS hT δ sc (∑ i ∈ s, F i) = ∑ i ∈ s, xiN θ S T hS hT δ sc (F i) := by
  funext z
  simp only [xiN, Finset.sum_apply, Finset.mul_sum]

theorem cartan_of_gram (V : HSp D) (hV : V.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) 1 := by
  have e : gramAt D V τ = 1 := by
    unfold gramAt; rw [hV]; exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [e]
  exact ⟨by simp, by simp, by
    open scoped ComplexOrder in simpa using Matrix.PosDef.one⟩

theorem toHom_sub (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b)
    (γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    toHom S T hS hT (γ - γ') = toHom S T hS hT γ - toHom S T hS hT γ' := by
  unfold toHom
  rw [← map_sub]
  rfl

theorem heisO_add_two (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {x l : WO S T} {X : WO S T → ℂ}
    (h2 : heisO ψ S T (2 • l) X = X) (hph : ψ (symplO S T x l) = 1) :
    heisO ψ S T (x + 2 • l) X = heisO ψ S T x X := by
  have h1 := GlobalTheory.LatVac.heisO_heisO ψ x (2 • l) X
  rw [h2] at h1
  have h3 : ψ (symplOH S T x (2 • l)) = 1 := by
    rw [two_nsmul]
    have e : symplOH S T x (l + l) = symplOH S T x l + symplOH S T x l := by
      simp only [symplOH, GlobalTheory.LatVac.symplO_add_right, mul_add]
    rw [e, ψ.map_add_eq_mul]
    exact GlobalTheory.LatVac.char_half hph
  rw [h1, h3, one_smul]


set_option maxHeartbeats 1600000 in
theorem moves_reading : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ (ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC S ΛS' → IsSelfDualC T ΛT → IsSelfDualC T ΛT' → ∀ e, IsSplitIdem D e → ∀ (s : GA D S) (s' : GA D T), SuppAt e S s → SuppAt e T s' → ∀ x₀ y₀, IsDetAt e S s x₀ → IsDetAt e T s' y₀ → (∀ u : WO S T, u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u = actO S T s s' u₀) → ∀ A₁ A₂ : AddSubgroup (VCx D.what₂.Tau a b), (∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ embH (tauE D) δ (toHom S T hS hT γ) ∈ A₁)) → (∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ embH (tauE D) δ (toHom S T hS hT γ) ∈ A₂)) → (∀ z ∈ A₂, ∃ γ, z = embH (tauE D) δ (toHom S T hS hT γ)) → Formalism.L2.Th1.H.IsSelfDual (HV sc) A₂ → Formalism.L2.Th1.H.IsSemiChar (HV sc) A₁ (alV D.host.d sc) → Formalism.L2.Th1.H.IsSemiChar (HV sc) A₂ (alV D.host.d sc) → Formalism.L2.Th1.H.relIdx A₁ A₂ ≠ 0 → ∀ f, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f → xiN θ S T hS hT δ sc f ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc) A₁ → xiN θ S T hS hT δ sc (om (s, s') f) ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc) A₂ → xiN θ S T hS hT δ sc (om (s, s') f) ≠ 0 → xiN θ S T hS hT δ sc (om (s, s') f) = fun z => ((μ x₀ : ℂ))⁻¹ * (μ y₀ : ℂ) * Formalism.L2.Th1.H.inter (HV sc) (alV D.host.d sc) A₁ A₂ (xiN θ S T hS hT δ sc f) z := by
  intro D ψ θ S T a b hS hT δ sc hP μ om hW ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT' e he s s' hs hs' x₀ y₀ hx₀ hy₀ hmove
    A₁ A₂ hA₁ hA₂ hA₂γ hsd hα₁ hα₂ hidx f hf hfix₁ hfix₂ hne
  classical
  have hψ := hW.std
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he

  have hom := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T μ μ om hW hP.inf (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) _ _ _ _ s s' (fun τ => by rw [GlobalTheory.SplitScalar.compAt_mt he hs])
    (fun τ => by rw [GlobalTheory.SplitScalar.compAt_mt he hs']) hmove f hf
  have hdΛ : ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ u' ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      ψ (symplO S T u u') = 1 := fun u hu u' hu' => GlobalTheory.LatVac.char_sympl_eq_one hψ hΛS hΛT hu hu'
  have hdΛ' : ∀ u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ u' ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True),
      ψ (symplO S T u u') = 1 := fun u hu u' hu' => GlobalTheory.LatVac.char_sympl_eq_one hψ hΛS' hΛT' hu hu'
  have hst := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS ΛT _ he.1
  have hstc := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS ΛT _ he'.1
  have hst' := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS' ΛT' _ he.1
  have hstc' := @GlobalTheory.SplitScalar.idem_smul_mem D S T ΛS' ΛT' _ he'.1
  have hoff : ∀ u ∈ (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True),
      (1 - (e + cA D e)) • u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
    intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := (hmove u).1 hu
    rw [GlobalTheory.SplitScalar.off_smul_actO hs hs', sub_smul, add_smul, one_smul]
    exact sub_mem hu₀ (add_mem (hst _ hu₀) (hstc _ hu₀))
  have hfo : ∀ γ, GlobalTheory.AdTh.IsFinOf S T γ (GlobalTheory.LatVac.finTens 1 γ) := fun γ => (GlobalTheory.VacSign.isFinOf_iff _ _).2 rfl
  have hzsub : ∀ γ γ', embH (tauE D) δ (toHom S T hS hT γ) - embH (tauE D) δ (toHom S T hS hT γ') =
      embH (tauE D) δ (toHom S T hS hT (γ - γ')) := fun γ γ' => by rw [toHom_sub, map_sub]
  set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ
  set Λ' := (latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ'

  have : (A₁.addSubgroupOf A₂).FiniteIndex := ⟨hidx⟩
  letI : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := Fintype.ofFinite _
  have hch : ∀ c : A₂ ⧸ A₁.addSubgroupOf A₂, ∃ γ, ((Quotient.out c : A₂) : VCx D.what₂.Tau a b) =
      embH (tauE D) δ (toHom S T hS hT γ) := fun c => hA₂γ _ (Quotient.out c).2
  choose γc hγc using hch
  have hcov : ∀ u ∈ Λ', ∃ c ∈ (Finset.univ : Finset (A₂ ⧸ A₁.addSubgroupOf A₂)),
      u - GlobalTheory.LatVac.finTens 1 (γc c) ∈ Λ := by
    intro u hu
    obtain ⟨γ, l, hl, hl', hγ⟩ := GlobalTheory.LatApprox.exists_rat_sub_two_nsmul D S T ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT' u hu
    have hx' : GlobalTheory.LatVac.finTens 1 γ ∈ Λ' := by
      rw [show GlobalTheory.LatVac.finTens 1 γ = u - 2 • l by rw [← hγ, sub_sub_cancel]]
      exact sub_mem hu (nsmul_mem hl' 2)
    have hz : embH (tauE D) δ (toHom S T hS hT γ) ∈ A₂ := (hA₂ γ _ (hfo γ)).1 hx'
    refine ⟨QuotientAddGroup.mk (⟨_, hz⟩ : A₂), Finset.mem_univ _, ?_⟩
    have hq : embH (tauE D) δ (toHom S T hS hT γ) - embH (tauE D) δ (toHom S T hS hT (γc (QuotientAddGroup.mk (⟨_, hz⟩ : A₂)))) ∈ A₁ := by
      rw [← hγc]
      obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add (A₁.addSubgroupOf A₂) (⟨_, hz⟩ : A₂)
      rw [hh, AddSubgroup.coe_add, sub_add_cancel_left]
      exact neg_mem (AddSubgroup.mem_addSubgroupOf.1 h.2)
    rw [hzsub] at hq
    have h1 := (hA₁ _ _ (hfo _)).2 hq
    rw [GlobalTheory.AdTh.SplitClass.finTens_sub] at h1
    have e1 : u - GlobalTheory.LatVac.finTens 1 (γc (QuotientAddGroup.mk (⟨_, hz⟩ : A₂))) =
        2 • l + (GlobalTheory.LatVac.finTens 1 γ - GlobalTheory.LatVac.finTens 1 (γc (QuotientAddGroup.mk (⟨_, hz⟩ : A₂)))) := by
      rw [← hγ]; abel
    rw [e1]
    exact add_mem (nsmul_mem hl 2) h1
  obtain ⟨R, hR, hRu⟩ := GlobalTheory.AdTh.SplitClass.exists_reps Λ (fun u => u ∈ Λ' ∧ IsHalf e u) Finset.univ
    (fun c => GlobalTheory.LatVac.finTens 1 (γc c)) fun u hu => hcov u hu.1
  obtain ⟨R', hR', hRu'⟩ := GlobalTheory.AdTh.SplitClass.exists_reps Λ (fun u => u ∈ Λ' ∧ IsHalf (cA D e) u) Finset.univ
    (fun c => GlobalTheory.LatVac.finTens 1 (γc c)) fun u hu => hcov u hu.1
  have hRu2 : ∀ u ∈ Λ', IsHalf e u → ∃! v, v ∈ R ∧ u - v ∈ Λ := fun u hu hue => hRu u ⟨hu, hue⟩
  have hRu2' : ∀ u ∈ Λ', IsHalf (cA D e) u → ∃! v, v ∈ R' ∧ u - v ∈ Λ := fun u hu hue => hRu' u ⟨hu, hue⟩
  have hmain := GlobalTheory.SplitScalar.om_vacuum_eq_splitFac_smul_sum D ψ θ S T μ μ om hW hP.inf hP.sigS hP.sigT
    (fun _ => 1) (fun _ => 1) (cartan_of_gram S hP.gS) (cartan_of_gram T hP.gT) ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT'
    e he s s' hs hs' x₀ y₀ hx₀ hy₀ hmove R R' hR hRu2 hR' hRu2' f hf

  have hpair : ∀ p : WO S T × WO S T, ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ l : WO S T,
      p ∈ R ×ˢ R' → (l ∈ Λ ∧ l ∈ Λ' ∧ p.1 + p.2 - GlobalTheory.LatVac.finTens 1 γ = 2 • l) := by
    intro p
    by_cases hp : p ∈ R ×ˢ R'
    · obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
      obtain ⟨γ, l, h1, h2, h3⟩ := GlobalTheory.LatApprox.exists_rat_sub_two_nsmul D S T ΛS ΛS' ΛT ΛT' hΛS hΛS' hΛT hΛT' (p.1 + p.2)
        (add_mem (hR _ hu).1 (hR' _ hu').1)
      exact ⟨γ, l, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, 0, fun h => absurd h hp⟩
  choose γ l hγl using hpair
  have hxeq : ∀ p ∈ R ×ˢ R', GlobalTheory.LatVac.finTens 1 (γ p) = p.1 + p.2 - 2 • l p := fun p hp => by
    rw [← (hγl p hp).2.2, sub_sub_cancel]
  have hxΛ' : ∀ p ∈ R ×ˢ R', GlobalTheory.LatVac.finTens 1 (γ p) ∈ Λ' := by
    intro p hp
    obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
    rw [hxeq p hp]
    exact sub_mem (add_mem (hR _ hu).1 (hR' _ hu').1) (nsmul_mem (hγl p hp).2.1 2)
  have hwx : ∀ p ∈ R ×ˢ R', p.1 + p.2 = GlobalTheory.LatVac.finTens 1 (γ p) + 2 • l p := fun p hp => by
    rw [hxeq p hp, sub_add_cancel]
  have hz₂ : ∀ p ∈ R ×ˢ R', embH (tauE D) δ (toHom S T hS hT (γ p)) ∈ A₂ := fun p hp =>
    (hA₂ _ _ (hfo _)).1 (hxΛ' p hp)

  have hpf : ∀ p ∈ R ×ˢ R', heisO ψ S T p.1 (heisO ψ S T p.2 f) =
      ψ (symplOH S T p.1 p.2) • heisO ψ S T (GlobalTheory.LatVac.finTens 1 (γ p)) f := by
    intro p hp
    rw [GlobalTheory.LatVac.heisO_heisO, hwx p hp, heisO_add_two ψ (hf.2.lat.1 _ (hγl p hp).1)
      (hdΛ' _ (hxΛ' p hp) _ (hγl p hp).2.1)]

  have hph : ∀ p ∈ R ×ˢ R', ψ (symplOH S T p.1 p.2) = alV D.host.d sc (embH (tauE D) δ (toHom S T hS hT (γ p))) := by
    intro p hp
    obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
    have hF : heisO ψ S T p.1 (heisO ψ S T p.2 (om (s, s') f)) = om (s, s') f := by
      rw [hom.2.lat.2 _ he' p.2 (hR' _ hu').1 (hR' _ hu').2, hom.2.lat.2 _ he p.1 (hR _ hu).1 (hR _ hu).2]
    rw [GlobalTheory.LatVac.heisO_heisO, hwx p hp, heisO_add_two ψ (hom.2.lat.1 _ (hγl p hp).2.1)
      (hdΛ' _ (hxΛ' p hp) _ (hγl p hp).2.1)] at hF
    have hG := congrArg (xiN θ S T hS hT δ sc) hF
    rw [xiN_smul, GlobalTheory.AdForm.HeisRead.xiN_heisO_finOf D ψ θ S T a b hS hT δ sc hP _ hom.2.theta _ _ (hfo _)] at hG
    obtain ⟨w, hw⟩ := Function.ne_iff.1 hne
    have h1 := congrFun hG w
    have h2 := hfix₂ _ (hz₂ p hp) w
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 hw
    have hU : Formalism.L2.Th1.H.opU (HV sc) (embH (tauE D) δ (toHom S T hS hT (γ p))) (xiN θ S T hS hT δ sc (om (s, s') f)) w ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1
      exact hw h1.symm
    exact mul_right_cancel₀ hU (h1.trans h2.symm)

  have hinj : ∀ p ∈ R ×ˢ R', ∀ q ∈ R ×ˢ R', embH (tauE D) δ (toHom S T hS hT (γ p)) -
      embH (tauE D) δ (toHom S T hS hT (γ q)) ∈ A₁ → p = q := by
    intro p hp q hq hpq
    rw [hzsub] at hpq
    have h1 := (hA₁ _ _ (hfo _)).2 hpq
    rw [GlobalTheory.AdTh.SplitClass.finTens_sub] at h1
    obtain ⟨hu, hu'⟩ := Finset.mem_product.1 hp
    obtain ⟨hv, hv'⟩ := Finset.mem_product.1 hq
    by_contra hne'
    refine GlobalTheory.SplitScalar.sum_sub_notMem he hst hstc hR hRu2 hR' hRu2' hu hv hu' hv'
      (by rw [Prod.mk.eta, Prod.mk.eta]; exact hne') ?_
    have e2 : p.1 + p.2 - (q.1 + q.2) = (GlobalTheory.LatVac.finTens 1 (γ p) - GlobalTheory.LatVac.finTens 1 (γ q)) +
        2 • (l p - l q) := by
      rw [hwx p hp, hwx q hq]; abel
    rw [e2]
    exact add_mem h1 (nsmul_mem (sub_mem (hγl p hp).1 (hγl q hq).1) 2)
  have hsurj : ∀ y ∈ A₂, ∃ p ∈ R ×ˢ R', y - embH (tauE D) δ (toHom S T hS hT (γ p)) ∈ A₁ := by
    intro y hy
    obtain ⟨γ₀, rfl⟩ := hA₂γ y hy
    have hv : GlobalTheory.LatVac.finTens 1 γ₀ ∈ Λ' := (hA₂ _ _ (hfo _)).2 hy
    have hh1 : IsHalf e (e • GlobalTheory.LatVac.finTens 1 γ₀) :=
      (GlobalTheory.SplitScalar.isHalf_iff _ _).2 (by rw [smul_smul, he.1])
    have hh2 : IsHalf (cA D e) (cA D e • GlobalTheory.LatVac.finTens 1 γ₀) :=
      (GlobalTheory.SplitScalar.isHalf_iff _ _).2 (by rw [smul_smul, he'.1])
    obtain ⟨r, ⟨hr, hrΛ⟩, -⟩ := hRu2 _ (hst' _ hv) hh1
    obtain ⟨r', ⟨hr', hrΛ'⟩, -⟩ := hRu2' _ (hstc' _ hv) hh2
    have hp : (r, r') ∈ R ×ˢ R' := Finset.mem_product.2 ⟨hr, hr'⟩
    refine ⟨(r, r'), hp, ?_⟩
    rw [hzsub]
    refine (hA₁ _ _ (hfo _)).1 ?_
    rw [GlobalTheory.AdTh.SplitClass.finTens_sub, hxeq _ hp]
    have e3 : GlobalTheory.LatVac.finTens 1 γ₀ - ((r, r').1 + (r, r').2 - 2 • l (r, r')) =
        (e • GlobalTheory.LatVac.finTens 1 γ₀ - r) + (cA D e • GlobalTheory.LatVac.finTens 1 γ₀ - r') +
        (1 - (e + cA D e)) • GlobalTheory.LatVac.finTens 1 γ₀ + 2 • l (r, r') := by
      simp only [sub_smul, add_smul, one_smul]; abel
    rw [e3]
    exact add_mem (add_mem (add_mem hrΛ hrΛ') (hoff _ hv)) (nsmul_mem (hγl _ hp).1 2)
  have hsum := GlobalTheory.ThetaInter.inter_eq_sum_reps (HV sc) (alV D.host.d sc) A₁ A₂ (herm_HV sc) hsd hα₁ hα₂ (R ×ˢ R')
    (fun p => embH (tauE D) δ (toHom S T hS hT (γ p))) hz₂ hinj hsurj _ hfix₁

  have hF : xiN θ S T hS hT δ sc (om (s, s') f) =
      ((splitFacO μ μ x₀ y₀ : ℂ) * ((Real.sqrt ((R.card : ℝ) * R'.card) : ℝ) : ℂ)⁻¹) •
      ∑ p ∈ R ×ˢ R', alV D.host.d sc (embH (tauE D) δ (toHom S T hS hT (γ p))) •
        Formalism.L2.Th1.H.opU (HV sc) (embH (tauE D) δ (toHom S T hS hT (γ p))) (xiN θ S T hS hT δ sc f) := by
    rw [hmain, xiN_smul, ← Finset.sum_product', xiN_sum]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hpf p hp, xiN_smul, GlobalTheory.AdForm.HeisRead.xiN_heisO_finOf D ψ θ S T a b hS hT δ sc hP _ hf.2.theta _ _ (hfo _),
      hph p hp]
  funext w
  rw [hF, hsum w]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, splitFacO, Circle.coe_mul, Circle.coe_inv,
    Finset.card_product, Nat.cast_mul]
  ring

end GlobalTheory.AdForm.SplitGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHEqZeroOfHO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumVac

variable {D : D7}

theorem symplOH_eq_zero_of_hO {S T : HSp D} {u u' : WO S T} (h : hO S T u u' = 0) : symplOH S T u u' = 0 := by
  rw [symplOH, symplO, h, mul_zero, map_zero, mul_zero]

theorem heisO_sum_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (f : WO S T → ℂ)
    (hf : IsLatVac (heisO ψ S T) Λ f) (hΛ : ∀ w : AE D, finPart D w ∈ intAE D → ∀ u ∈ Λ, w • u ∈ Λ)
    {ι : Type} (p : ι → AE D) (s : Finset ι) (hs : ∀ i ∈ s, IsSplitIdem D (p i))
    (hc : ∀ i ∈ s, ∀ j ∈ s, p i * cA D (p j) = 0) (x : WO S T) (hx : x ∈ Λ) :
    heisO ψ S T ((∑ i ∈ s, p i) • x) f = f := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, zero_smul]; exact GlobalTheory.LatVac.heisO_zero ψ f
  | insert a s ha ih =>
    have hsa := hs a (Finset.mem_insert_self _ _)
    have ih' := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    have hmem : p a • x ∈ Λ := hΛ _ (GlobalTheory.SplitHomLattice.idem_int hsa) x hx
    have hhalf : IsHalf (p a) (p a • x) := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hsa.1]
    have h1 : heisO ψ S T (p a • x) f = f := hf.2 (p a) hsa _ hmem hhalf
    have hz : hO S T (p a • x) ((∑ i ∈ s, p i) • x) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [GlobalTheory.LatVacSign.hO_smul_smul, map_sum, Finset.mul_sum,
        Finset.sum_eq_zero (fun j hj => hc a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)),
        zero_mul]
    have key := GlobalTheory.LatVac.heisO_heisO ψ (p a • x) ((∑ i ∈ s, p i) • x) f
    rw [ih', h1, symplOH_eq_zero_of_hO hz, ψ.map_zero_eq_one, one_smul, ← add_smul] at key
    rw [Finset.sum_insert ha]
    exact key.symm

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨he1, he2, v, ε, hpl, he3⟩ := he
  exact ⟨by rw [← RingHom.map_mul, he1], by rw [GlobalTheory.LatVac.cA_cA, mul_comm, he2], v, ε, hpl,
    by rw [GlobalTheory.LatVac.cA_cA, add_comm, he3]⟩

theorem heisO_idemSum_fix : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T))
    (f : WO S T → ℂ), IsLatVac (heisO ψ S T) Λ f → (∀ w : AE D, finPart D w ∈ intAE D → ∀ u ∈ Λ, w • u ∈ Λ) →
    ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ x ∈ Λ,
      heisO ψ S T (e • x) f = f ∧ heisO ψ S T (cA D e • x) f = f := by
  intro D ψ S T Λ f hf hΛ e SS he x hx
  obtain ⟨⟨es, hes, rfl⟩, hce⟩ := he
  have h1 : ∀ i ∈ SS, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ SS, ∀ j ∈ SS, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es SS h1 hce
  refine ⟨heisO_sum_smul ψ S T Λ f hf hΛ es SS (fun i hi => (hes i hi).1) hcross x hx, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine heisO_sum_smul ψ S T Λ f hf hΛ (fun i => cA D (es i)) SS (fun i hi => isSplitIdem_cA (hes i hi).1)
    (fun i hi j hj => ?_) x hx
  rw [← RingHom.map_mul, hcross i hi j hj, map_zero]

end GlobalTheory.IdemSumVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFourierSumEqSumHeisenbergTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfFourier

theorem thetaAt_eq_sum_heis_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ) (ι : Type) (s : Finset ι) (K : ι → ℂ) (xs ys : ι → WO S T) (k : ℕ), 0 < k → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → (∀ i ∈ s, IsHalf e (xs i)) → (∀ i ∈ s, IsHalf (cA D e) (ys i)) → (∀ i ∈ s, ∀ u ∈ Λ, ψ (symplO S T (k • u) (ys i)) = 1) → (∀ t, Φ t = ∑ i ∈ s, K i * (ψ (symplO S T (t + xs i) (ys i)) * halfInd e Λ (t + xs i))) → f = ∑ i ∈ s, K i • heisO ψ S T (xs i) (heisO ψ S T (ys i) f₀) := by
  intro D ψ S T e Λ f₀ Φ f ι s K xs ys k hk hθ hx hy hΛ hΦ
  classical
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  have hvac : Tm (halfInd e Λ) = f₀ := by simpa using hTm.vac

  set g : ι → WO S T → ℂ := fun i t => ψ (symplO S T t (ys i)) * halfInd e Λ t with hg
  have hhalf : ∀ t, halfInd e Λ t ≠ 0 → t ∈ Λ ∧ IsHalf e t := by
    intro t ht
    by_contra h
    exact ht (by simp [halfInd, h])
  have hSB : ∀ i ∈ s, IsSBHalf e Λ (g i) := by
    intro i hi
    refine ⟨fun t ht => ?_, k, hk, fun u hu hh t => ?_, fun t ht => ?_⟩
    · exact (hhalf t (right_ne_zero_of_mul ht)).2
    · have hku : k • u ∈ Λ := Λ.nsmul_mem hu k
      have hkh : IsHalf e (k • u) := by
        intro a b
        change e * ((k • u : Matrix _ _ (AE D)) a b) = (k • u : Matrix _ _ (AE D)) a b
        rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hh a b]
      have hind : halfInd e Λ (t + k • u) = halfInd e Λ t := by
        have : (t + k • u ∈ Λ ∧ IsHalf e (t + k • u)) ↔ (t ∈ Λ ∧ IsHalf e t) := by
          rw [Λ.add_mem_cancel_right hku]
          refine and_congr_right fun _ => forall_congr' fun a => forall_congr' fun b => ?_
          rw [Matrix.add_apply, mul_add, hkh a b, add_left_inj]
        simp only [halfInd, this]
      simp only [hg, hind, GlobalTheory.LatVac.symplO_add_left, AddChar.map_add_eq_mul, hΛ i hi u hu, mul_one]
    · exact Λ.nsmul_mem (hhalf t (right_ne_zero_of_mul ht)).1 k
  have hΦ' : Φ = ∑ i ∈ s, K i • fun t => g i (t + xs i) := by
    funext t
    rw [hΦ t, Finset.sum_apply]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hall Tm hTm, hΦ', map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, hTm.trans _ (hSB i hi) (xs i) (hx i hi)]
  congr 2
  have : g i = fun t => ψ (symplO S T t (ys i)) * halfInd e Λ t := rfl
  rw [this, hTm.modul _ (GlobalTheory.isSBHalf_halfInd e Λ) (ys i) (hy i hi), hvac]

end GlobalTheory.HalfFourier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairs
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.StdStepsT

theorem stdPair_steps_all : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → (∀ (i : ℕ), i + 1 ≤ B.R.m → StdPair θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) I.A.δ I.A.sc ψ) ∧ (I.rec7 l Z).sp.X'.gram = 1 ∧ (∀ τ, B.fields.embC I.A.σ₀ τ = tauE (I.rec7 l Z) τ) ∧ (∀ τ, I.J.cD τ ≠ 0) ∧ ∀ (V : HSp (I.rec7 l Z)) (g : GA (I.rec7 l Z) V), ∃ x, IsDetRoot V g x := by
  intro B X I hI hP l Z ψ θ hψ hθ
  obtain ⟨hs, hX, hX', -⟩ := hI.spaces
  have oX : ∀ j, GlobalTheory.Mem.Col2.Crd.Ortho (B.sp.X j) := fun j => by rw [hX]; exact GlobalTheory.Mem.Col2.Crd.ortho_pos hs _
  have oX' : GlobalTheory.Mem.Col2.Crd.Ortho B.sp.X' := by rw [hX']; exact GlobalTheory.Mem.Col2.Crd.ortho_pos hs _
  have gX : ∀ j, (B.sp.X j).gram = 1 := fun j => by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.one_apply]
    exact (oX j).1 a b
  have gX' : B.sp.X'.gram = 1 := by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.one_apply]
    exact oX'.1 a b
  have hcc : (I.rec7 l Z).host.ccK = ⊤ := B.toPre.ccK_top
  refine ⟨fun i hi => ?_, gX', fun τ => B.fields_embC τ, GlobalTheory.Mem.Col2.DgenNe.dgen_ne_zero B.host I.J.cD hI.amb_ok.dgen,
    fun V g => GlobalTheory.RecDict.exists_isDetRoot _ V g⟩
  have r1 := rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)
  have r2 := rankN (I.rec7 l Z) (i + 1) hi
  refine ⟨hψ, hθ, gX i, gX (i + 1), (I.rec7 l Z).sp.X_sig i, (I.rec7 l Z).sp.X_sig (i + 1), ?_, hcc, I.J.δ_ne_zero,
    GlobalTheory.AdForm.StdSteps.realPlace_cmTrace_zero_element_eq_I_mul_abs _ hcc, GlobalTheory.AdForm.StdSteps.scale_eq (I.rec7 l Z) I.J.δ_ne_zero⟩
  rw [r1, r2]
  exact ⟨Ranks.N_pos _ _, GlobalTheory.AdForm.StdSteps.N_lt_succ _ _, GlobalTheory.AdForm.StdSteps.even_N _ _, GlobalTheory.AdForm.StdSteps.even_N _ _⟩

end GlobalTheory.AdForm.StdStepsT
end

