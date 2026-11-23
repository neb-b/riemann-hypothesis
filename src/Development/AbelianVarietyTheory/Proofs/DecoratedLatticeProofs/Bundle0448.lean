module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiVacuumOperatorZeroOrLeftInvertible
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0442
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0331
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0317

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameCoordsMemSelfDualLatticeCoordsIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LineSelfDual

theorem hT_frame (D : D7) (S : HSp D) (u v : S.V) :
    S.hT u v = ∑ i, ∑ j, star (S.frame.equivFun u i) * S.gram i j * S.frame.equivFun v j := by
  conv_lhs => rw [← S.frame.sum_repr u, ← S.frame.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.equivFun_apply, Formalism.BasicNotions.HSpace.gram, starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

noncomputable def selfDualLatticeCoordsInHermitianFrame (D : D7) (S : HSp D) : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E) :=
  S.L0.map (S.frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap

theorem frameCoords_mem_selfDualLatticeCoords_iff (D : D7) (S : HSp D) (u : S.V) : S.frame.equivFun u ∈ selfDualLatticeCoordsInHermitianFrame D S ↔ u ∈ S.L0 :=
  ⟨fun ⟨z, hz, e⟩ => S.frame.equivFun.injective e ▸ hz, fun hu => ⟨u, hu, rfl⟩⟩

theorem isSelfDualC_selfDualLatticeCoordsInFrame (D : D7) (S : HSp D) : IsSelfDualC S (selfDualLatticeCoordsInHermitianFrame D S) := by
  refine ⟨⟨S.standardTuple_isLattice.fg.map _, ?_⟩, ?_⟩
  · exact fun _ _ => (LinearIndependent.iff_fractionRing (𝓞 D.host.E) D.host.E).mp
  · intro y
    obtain ⟨v, rfl⟩ := S.frame.equivFun.surjective y
    have h2 : v ∈ S.L0 ↔ ∀ u ∈ S.L0, S.hT u v ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      conv_lhs => rw [← show Formalism.HermitianLatticesTheory.dual S.hT S.L0 = S.L0 from S.baseLattice_isUnimodular]
      simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
    have h3 : ∀ z : D.host.E, z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ ∃ b : 𝓞 D.host.E, (b : D.host.E) = z :=
      fun z => Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha⟩⟩
    rw [frameCoords_mem_selfDualLatticeCoords_iff, h2]
    constructor
    · rintro H _ ⟨u, hu, rfl⟩
      have := (h3 _).1 (H u hu)
      rwa [hT_frame] at this
    · intro H u hu
      rw [h3, hT_frame]
      exact H _ ⟨u, hu, rfl⟩

end GlobalTheory.LineSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationEqOnVacuaOfEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.Transfer

theorem af_ext'' {D : D7} {x y : Af D.host.F} (h : ∀ w, evalV D.host.F w x = evalV D.host.F w y) : x = y :=
  Subtype.ext (funext fun w => h w)

theorem latO_signs : ∀ (D : D7) (r : ℕ) (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (q i).v) → (∀ p, P p ↔ ∃ i, (q i).v = p) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P, ∃ ε : ℂ, ε * ε = 1 ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT P f → heisO ψ S T x f = ε • f := by
  intro D r k _ _ _ _ p P hinj hmem ψ hψ S T LS LT hS hT x hx
  have hΛ : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P,
      ∀ u' ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P,
        ψ (symplO S T u u') = 1 := fun u hu u' hu' =>
    (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT P u (GlobalTheory.FinPl.LatMem.latO_mxAt hu)).1 hu u' hu'
  let G := GlobalTheory.LatVac.signGroup ψ _ hΛ
    (IsLatVac (heisO ψ S T) (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P))
  have half : ∀ e, IsSplitIdem D e →
      ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P, IsHalf e u → u ∈ G :=
    fun e he u hu hh => ⟨hu, 1, one_mul _, fun f hf => by rw [hf.2 e he u hu hh, one_smul]⟩
  have splitC : ∀ e, IsSplitIdem D e → IsSplitIdem D (cA D e) := by
    rintro e ⟨he1, he2, v, ε, hpl, he3⟩
    exact ⟨by rw [← RingHom.map_mul, he1], by rw [GlobalTheory.LatVac.cA_cA, mul_comm, he2], v, ε, hpl,
      by rw [GlobalTheory.LatVac.cA_cA, add_comm, he3]⟩
  have hsub : ∀ i, latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v) ≤
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P := by
    intro i
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hs, rest⟩
    exact ⟨α, hα, fun v hv => hs v fun h => hv ((hmem v).2 ⟨i, h.symm⟩), rest⟩
  have piece : ∀ i, ∀ w ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v),
      w ∈ G := by
    intro i w hw
    obtain ⟨h1, h2⟩ := GlobalTheory.SplitVac.idem_latO D (k i) (p i) S T LS LT w hw
    have he := (p i).split
    have hee : (p i).e * (p i).e = (p i).e := he.1
    have hz : (Matrix.of fun a b => cA D (p i).e * w a b : WO S T) = w - Matrix.of fun a b => (p i).e * w a b := by
      ext a b
      rw [Matrix.of_apply, Matrix.sub_apply, Matrix.of_apply, eq_sub_iff_add_eq', ← add_mul, h2]
    have hyG : (Matrix.of fun a b => (p i).e * w a b : WO S T) ∈ G :=
      half _ he _ (hsub i h1) fun a b => by rw [Matrix.of_apply, ← mul_assoc, hee]
    have hzG : (Matrix.of fun a b => cA D (p i).e * w a b : WO S T) ∈ G := by
      refine half _ (splitC _ he) _ ?_ fun a b => ?_
      · rw [hz]; exact sub_mem (hsub i hw) (hsub i h1)
      · rw [Matrix.of_apply, ← mul_assoc, ← RingHom.map_mul, hee]
    rw [hz] at hzG
    simpa using add_mem hyG hzG
  have hxG : x ∈ G := by
    induction hx using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩ := hw
      have hdec : α = ∑ i : Fin r, GlobalTheory.FinPl.LatMem.indP D.host.F (· = (p i).v) * α := by
        apply af_ext''
        intro v
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [map_mul, GlobalTheory.FinPl.LatMem.evalV_indP]
        by_cases hv : P v
        · obtain ⟨i, rfl⟩ := (hmem v).1 hv
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hj
            rw [if_neg (fun h => hj (hinj h).symm), zero_mul]
          · intro h
            exact absurd (Finset.mem_univ i) h
        · rw [hsupp v hv]
          simp
      rw [hdec]
      refine Finset.sum_induction _ (fun β : Af D.host.F => (Matrix.of fun i j =>
          (pairA D.host.F 0 β) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) ∈ G)
        (fun β γ hβ hγ => ?_) ?_ (fun i _ => ?_)
      · have e : (Matrix.of fun i j => (pairA D.host.F 0 (β + γ)) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) :
            WO S T) = (Matrix.of fun i j => (pairA D.host.F 0 β) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) +
            Matrix.of fun i j => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) := by
          ext i j
          rw [Matrix.add_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, GlobalTheory.LatVac.pair_add,
            TensorProduct.add_tmul]
        rw [e]
        exact add_mem hβ hγ
      · have e : (Matrix.of fun i j => (pairA D.host.F 0 (0 : Af D.host.F)) ⊗ₜ[D.host.F]
            (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) = 0 := by
          ext i j
          rw [Matrix.of_apply, Matrix.zero_apply]
          exact TensorProduct.zero_tmul _ _
        rw [e]
        exact zero_mem _
      · refine piece i _ (AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.mul_mem_intAf
          (GlobalTheory.FinPl.LatMem.indicatorAdele_mem_integralAdeles' D.host.F _) hα, fun v hv => ?_, a, ha, s, hs, t, ht, rfl⟩)
        rw [map_mul, GlobalTheory.FinPl.LatMem.indicatorAdele_supported D.host.F _ v hv, zero_mul]
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  obtain ⟨-, ε, hε, h⟩ := hxG
  exact ⟨ε, hε, fun f hf => h f hf.2⟩

def heisLin {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := heisO ψ S T x
  map_add' f g := by
    funext w
    simp only [heisO, Pi.add_apply]
    ring
  map_smul' c f := GlobalTheory.LatVac.heisO_smul ψ x c f

def suppGrp {D : D7} (S T : HSp D) (P : GlobalTheory.FinPl.Pl D → Prop) : AddSubgroup (WO S T) where
  carrier := {x | GlobalTheory.FinPl.MxAt P x}
  zero_mem' := fun _ _ => zero_mem (GlobalTheory.FinPl.idAt D P)
  add_mem' := fun hx hy i j => add_mem (hx i j) (hy i j)
  neg_mem' := fun hx i j => neg_mem (hx i j)

theorem heis_comm {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x γ : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T γ (heisO ψ S T x f) = ψ (symplO S T γ x) • heisO ψ S T x (heisO ψ S T γ f) := by
  rw [GlobalTheory.LatVac.heisO_heisO, GlobalTheory.LatVac.heisO_heisO, smul_smul, add_comm x γ, ← AddChar.map_add_eq_mul,
    ← GlobalTheory.ZeroOrInv.symplOH_two S T γ x]
  have h : symplOH S T γ x + symplOH S T x γ = 0 := by
    have h1 := GlobalTheory.ZeroOrInv.symplO_skew' S T γ x
    unfold symplOH
    rw [h1, mul_neg, add_neg_cancel]
  rw [add_assoc, h, add_zero]

theorem comb_sub {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c₁ c₂ : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    ∑ x ∈ (c₁ - c₂).support, (c₁ - c₂) x • heisLin ψ S T x f = comb ψ S T c₁ f - comb ψ S T c₂ f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, GlobalTheory.HeisComb.comb_eq_sum,
    ← Finsupp.sum_sub_index (fun a b₁ b₂ => sub_smul b₁ b₂ (heisO ψ S T a f))]
  rfl

theorem comb_eq_on_vacua : ∀ (D : D7) (r : ℕ) (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (q i).v) → (∀ p, P p ↔ ∃ i, (q i).v = p) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ c₁ c₂ : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt P c₁ → GlobalTheory.FinPl.CombAt P c₂ → ∀ f₀, GlobalTheory.FinPl.Vac ψ S T LS LT P f₀ → f₀ ≠ 0 → comb ψ S T c₁ f₀ = comb ψ S T c₂ f₀ → ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT P f → comb ψ S T c₁ f = comb ψ S T c₂ f := by
  intro D r k _ _ _ _ q P hinj hmem ψ hψ S T LS LT hS hT c₁ c₂ h₁ h₂ f₀ hf₀ hne heq f hf
  let Γ : AddSubgroup (WO S T) := latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P
  have hΓG : Γ ≤ suppGrp S T P := fun x hx => GlobalTheory.FinPl.LatMem.latO_mxAt hx
  have hex : ∀ γ : WO S T, ∃ s : ℂ, γ ∈ Γ →
      s ≠ 0 ∧ ∀ g ∈ {g | GlobalTheory.FinPl.Vac ψ S T LS LT P g}, heisLin ψ S T γ g = s • g := by
    intro γ
    by_cases hγ : γ ∈ Γ
    · obtain ⟨ε, hε, h⟩ := latO_signs D r k q P hinj hmem ψ hψ S T LS LT hS hT γ hγ
      exact ⟨ε, fun _ => ⟨left_ne_zero_of_mul_eq_one hε, h⟩⟩
    · exact ⟨1, fun h => absurd h hγ⟩
  choose aF haF using hex
  have hχ : ∀ x : WO S T, ∀ γ ∈ Γ, ∀ γ' ∈ Γ, ψ (symplO S T γ (x + γ')) = ψ (symplO S T γ x) := by
    intro x γ hγ γ' hγ'
    rw [GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul,
      (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT P γ (hΓG hγ)).1 hγ γ' hγ', mul_one]
  have hsep : ∀ x ∈ suppGrp S T P, ∀ y ∈ suppGrp S T P, x - y ∉ Γ →
      ∃ γ ∈ Γ, ψ (symplO S T γ x) ≠ ψ (symplO S T γ y) := by
    intro x hx y hy h
    have hd : x - y ∈ suppGrp S T P := sub_mem hx hy
    rw [GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT P (x - y) hd] at h
    push_neg at h
    obtain ⟨l, hl, hl'⟩ := h
    refine ⟨l, hl, fun he => hl' ?_⟩
    rw [← sub_add_cancel x y, GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul] at he
    have h1 : ψ (symplO S T l (x - y)) = 1 :=
      mul_right_cancel₀ (GlobalTheory.ZeroOrInv.psi_ne_zero ψ _) (he.trans (one_mul _).symm)
    rw [GlobalTheory.ZeroOrInv.symplO_skew'] at h1
    exact GlobalTheory.ZeroOrInv.psi_eq_one_of_neg ψ h1
  have hJ : ∀ x ∈ (c₁ - c₂).support, x ∈ suppGrp S T P := by
    intro x hx
    rcases Finset.mem_union.1 (Finsupp.support_sub hx) with h | h
    · exact h₁ x h
    · exact h₂ x h
  rcases GlobalTheory.isolate_abstract (WO S T) Γ (suppGrp S T P) (WO S T → ℂ) (heisLin ψ S T)
      {g | GlobalTheory.FinPl.Vac ψ S T LS LT P g} (fun x y => ψ (symplOH S T x y)) aF (fun x γ => ψ (symplO S T γ x)) hΓG
      (GlobalTheory.LatVac.heisO_zero ψ) (GlobalTheory.LatVac.heisO_heisO ψ) (fun _ _ => GlobalTheory.ZeroOrInv.psi_ne_zero ψ _)
      (fun γ hγ => haF γ hγ) (fun γ _ x v => heis_comm ψ S T x γ v) hχ hsep
      (c₁ - c₂).support (DFunLike.coe (c₁ - c₂)) hJ with h | ⟨κ, -, hinv⟩
  · have h0 := h f hf
    rwa [comb_sub, sub_eq_zero] at h0
  · have h0 := hinv f₀ hf₀
    rw [comb_sub, heq, sub_self] at h0
    simp only [map_zero, smul_zero, Finset.sum_const_zero] at h0
    exact absurd h0.symm hne

end GlobalTheory.FinPl.Transfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HypsSatisfiable
section
noncomputable section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn.Inhab

theorem weil_exists : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ lam : D.host.F, lam ≠ 0 → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∃ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch (shift ψ lam) χ θ V μ ω := by
  intro D n V ψ hψ lam hlam χ hχ hr θ hθ μ 𝓕 hμ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  have hlamE : algebraMap D.host.F D.host.E lam ≠ 0 := (map_ne_zero _).2 hlam
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  set μ' : D.host.E := -D.host.xi0 / algebraMap D.host.F D.host.E lam with hμ'
  have hsk : IsSkew μ' := by
    refine ⟨div_ne_zero (neg_ne_zero.2 hxi) hlamE, ?_⟩
    rw [hμ', star_div₀, star_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, Formalism.IndefR.Eqv.star_algebraMapF]
    ring
  have hl : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ' := by
    rw [hμ']; field_simp
  obtain ⟨κ, hκ⟩ := GlobalTheory.StdUnn.chart_exists D A μ' hsk
  obtain ⟨hχi, hri⟩ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χ V.rank hχ hr
  have hr1 : ResEta D 1 (dblSp A).rank := by
    have := GlobalTheory.Eis.SimplePoleModel.resEta_one_two_mul D A.rank
    convert this using 2
    simp [GlobalTheory.Doubling.dblSp]
    omega
  obtain ⟨omh, homh⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ (dblSp A) V 1 χ⁻¹ hψ
    ⟨continuous_const, fun _ => rfl⟩ hχi hr1 hri
  obtain ⟨omS, hS⟩ := GlobalTheory.StdUnn.exists_transport_std D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ κ
  refine ⟨omS, ⟨?_, ?_, ?_⟩⟩
  · intro g a hg Φ x
    have := GlobalTheory.StdUnn.transport_levi D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ μ' hsk κ hκ omS hS lam hl g a hg Φ x
    rw [inv_inv] at this
    exact this
  · intro g b hg Φ x
    exact GlobalTheory.StdUnn.Unip.transport_unip D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ μ' hsk κ hκ omS hS lam hl g b hg Φ x
  · intro g hg Φ x
    exact GlobalTheory.StdUnn.WeylStd.main D ψ A V χ⁻¹ omh homh μ 𝓕 hμ θ hθ μ' hsk κ hκ omS hS lam hl g hg Φ x

theorem fock_gauss (hg : ∀ (D : D7) (n : ℕ) (V : HSp D) (l : D.what₂.Tau → ℝ), (∀ τ, l τ ≠ 0) → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∃ f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ, ∀ z, f z = gauss V l s (fun τ => Matrix.of (z τ))) : ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ), (∀ τ, l τ ≠ 0) → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ U : Set (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U → IsCompact U → (0 : Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∈ U → ∃ Φ : schwartzA θ V.rank n, Φ.1 = (fun x => gauss V l s (fun τ => compAt θ τ x) * U.indicator 1 (fun i j => finPart D (x i j))) ∧ Φ.1 ∈ fockA θ V n l s ∧ Φ.1 0 ≠ 0 := by
  intro D n V θ l hl s hs U hUo hUc h0
  obtain ⟨f, hf⟩ := hg D n V l hl s hs
  set g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := U.indicator 1 with hgdef
  have hgSB : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
    refine ⟨?_, ?_⟩
    · exact (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hUo).isLocallyConstant
    · exact HasCompactSupport.intro' hUc hUo.isClosed (fun x hx => Set.indicator_of_notMem hx _)
  have hmem : (fun x : Mx D V.rank n => gauss V l s (fun τ => compAt θ τ x) * g (fun i j => finPart D (x i j))) ∈ schwartzA θ V.rank n := by
    refine Submodule.subset_span ⟨f, g, hgSB, ?_⟩
    funext x
    rw [hf]
    rfl
  refine ⟨⟨_, hmem⟩, rfl, ?_, ?_⟩
  · refine Submodule.subset_span ⟨1, g, hgSB, ?_⟩
    funext x
    simp [evalPoly]
  · show gauss V l s (fun τ => compAt θ τ 0) * g (fun i j => finPart D ((0 : Mx D V.rank n) i j)) ≠ 0
    have h1 : (fun τ => compAt θ τ (0 : Mx D V.rank n)) = fun _ => 0 := by
      funext τ; ext i j; simp [compAt]
    have h2 : (fun i j => finPart D ((0 : Mx D V.rank n) i j)) = 0 := by
      funext i j; simp
    rw [h1, h2, hgdef, Set.indicator_of_mem h0]
    simp [gauss]

end GlobalTheory.StdUnn.Inhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFrameMatrixIffMemSplitHalfHomLattice
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def frameAt {N : ℕ} (π' : EAf D →+* k) (β : GL (Fin N) (EAf D)) : GlobalTheory.LocMod.Frame k N (Fin N) where
  β := β.val.map π'
  γ := (β⁻¹).val.map π'
  βγ := by rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  γβ := by rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

variable {S T : HSp D} (q : GlobalTheory.FinPl.SplitPt D k) {π' : EAf D →+* k}
  (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))

theorem down_eq (hπ : ∀ a, π' (toEAf D a) = q.pr a) (x : WO S T) :
    (ofSplit q).down (frameAt π' βS) (frameAt π' βT) x = (frMapO S T βS βT x).map π' := by
  have h2 : ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D)).map π' = x.map q.pr := Matrix.ext fun i j => hπ _
  rw [frMapO, Matrix.map_mul, Matrix.map_mul, h2]
  rfl

theorem up_down {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (p : Place D k)
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (t : WO S T) :
    p.up FS FT (p.down FS FT t) = p.e • t := by
  unfold Place.up Place.down
  have : FT.β * (FT.γ * (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ = t.map p.π := by
    simp only [← Matrix.mul_assoc, FT.βγ, Matrix.one_mul]
    rw [Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
  rw [this]
  exact Matrix.ext fun i j => p.ι_π _

theorem down_up {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (p : Place D k)
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (x : Matrix Y Y' k) :
    p.down FS FT (p.up FS FT x) = x := by
  unfold Place.up Place.down
  have : ((FT.β * x * FS.γ).map p.ι : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π = FT.β * x * FS.γ :=
    Matrix.ext fun i j => p.π_ι _
  rw [this]
  simp only [← Matrix.mul_assoc, FT.γβ, Matrix.one_mul]
  rw [Matrix.mul_assoc, FS.γβ, Matrix.mul_one]

theorem frMapO_smul (a : AE D) (x : WO S T) (i : Fin T.rank) (j : Fin S.rank) :
    frMapO S T βS βT (a • x) i j = toEAf D a * frMapO S T βS βT x i j := by
  have : (a • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D a • x.map (toEAf D) :=
    Matrix.ext fun i j => (toEAf D).map_mul _ _
  exact (congrArg (fun z => GlobalTheory.FunObj.Comparison₂.fr βT βS z i j) this).trans
    (congrFun (congrFun (GlobalTheory.FunObj.Comparison₂.fr_smul βT βS _ _) i) j)

theorem smul_mem_at {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {x : WO S T}
    (hx : x ∈ latO S T LS LT fun _ => True) : q.e • x ∈ latO S T LS LT (· = q.v) := by
  obtain ⟨ε, hε, h⟩ := q.above
  have h1 : IsPlaceIdem D q.v (pairA _ 0 (GlobalTheory.VacUnion.idemF q.v)) :=
    ⟨_, rfl, by rw [GlobalTheory.VacUnion.evalV_idemF, if_pos rfl], fun w hw => by rw [GlobalTheory.VacUnion.evalV_idemF, if_neg hw]⟩
  have h2 : GlobalTheory.VacUnion.idemE q.v = q.e + cA D q.e := by
    rw [h, GlobalTheory.IdemSupport.placeIdem_unique hε h1]; rfl
  have h3 := GlobalTheory.VacUnion.idemE_smul_mem q.v (GlobalTheory.PlaceModelSum.idem_smul_latO q.split.1 hx)
  have h4 : GlobalTheory.VacUnion.idemE q.v * q.e = q.e := by
    rw [h2]
    linear_combination q.split.1 + q.split.2.1
  rwa [smul_smul, h4] at h3

theorem latO_le_top {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} : latO S T LS LT P ≤ latO S T LS LT fun _ => True :=
  AddSubgroup.closure_mono fun _ ⟨α, hα, _, k⟩ => ⟨α, hα, fun _ hw => (hw trivial).elim, k⟩

theorem eq_sum {r : ℕ} {a : Fin r → AE D} {pl : Fin r → Formalism.L2.DIV.Pl D.host.E} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D}
    (ha : ∀ i, Formalism.L2.NTheta.IsIdemAt (a i) (pl i)) (hinj : Function.Injective pl) (hQ : ∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP)
    (he : IsIdemSum e Q) : e = ∑ i, a i := by
  obtain ⟨⟨es, h1, rfl⟩, -⟩ := he
  have hΦ := GlobalTheory.StdFrames.comp_toAd D
  refine (Finset.sum_bij (fun i _ => pl i) (fun i _ => (hQ _).2 ⟨i, rfl⟩) (fun i _ j _ h => hinj h)
    (fun PP hPP => by obtain ⟨i, hi⟩ := (hQ PP).1 hPP; exact ⟨i, Finset.mem_univ _, hi⟩) fun i _ => ?_).symm
  exact GlobalTheory.IdemSupport.delta_unique hΦ (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (ha i))
    (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (h1 _ ((hQ _).2 ⟨i, rfl⟩)))

theorem isIntM_iff_mem_latO : ∀ (D : D7) (r : ℕ) (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), (∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (pl i)) → (∀ i, (q i).UnitAA) → Function.Injective pl → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → IsIdemSum e Q → ∀ (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), (∀ i (π' : EAf D →+* k i), (∀ a, π' (toEAf D a) = (q i).pr a) → (∀ y : Fin S.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔ (fun a => (q i).sec ((βS.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV S LS (· = (q i).v)) ∧ ∀ y : Fin T.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔ (fun a => (q i).sec ((βT.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV T LT (· = (q i).v)) → ∀ x : WO S T, IsHalf e x → (IsIntM (frMapO S T βS βT x) ↔ x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D r k _ _ _ _ q pl Q e hq hu hinj hQ he S T LS LT hS hT βS βT hβ x hx
  choose π' hπ hrest using fun i => GlobalTheory.FinPl.SplitPt.exists_lift_isRed D (k i) (q i) (pl i) (hq i)
  have hint := fun i => (hrest i).2.1
  have he' : e = ∑ i, (q i).e := eq_sum hq hinj hQ he
  have hxe : e • x = x := Matrix.ext fun i j => hx i j
  constructor
  · intro h
    rw [← hxe, he', Finset.sum_smul]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have h1 := _root_.GlobalTheory.UpMem.up_mem_latO D (k i) (q i) (hu i) _ _ S T (frameAt (π' i) βS) (frameAt (π' i) βT) LS LT hS hT
      (hβ i _ (hπ i)).1 (hβ i _ (hπ i)).2 ((frMapO S T βS βT x).map (π' i)) fun a b => ((hint i _).1 (h a b)).2
    rw [← down_eq (q i) βS βT (hπ i), up_down] at h1
    exact latO_le_top h1
  · intro h a b
    rw [← hxe, frMapO_smul, he', GlobalTheory.FunObj.Comparison₂.hom_sum, Finset.sum_mul]
    refine Subring.sum_mem _ fun i _ => (hint i _).2 ⟨?_, ?_⟩
    · rw [← mul_assoc, sub_mul, one_mul, ← RingHom.map_mul, (q i).split.1, sub_self, zero_mul]
      exact zero_mem _
    · obtain ⟨y, hy, h1⟩ := _root_.GlobalTheory.HalfIntUp.exists_int_up D (k i) (q i) (hu i) _ _ S T (frameAt (π' i) βS) (frameAt (π' i) βT) LS LT hS hT
        (hβ i _ (hπ i)).1 (hβ i _ (hπ i)).2 _ (smul_mem_at (q i) h)
        (fun a b => by
          change (q i).e * ((q i).e * _) = (q i).e * _
          rw [← mul_assoc, (q i).split.1])
      have h2 := down_eq (q i) βS βT (hπ i) ((q i).e • x)
      rw [h1, down_up, ← h1] at h2
      rw [← frMapO_smul]
      have h3 := hy a b
      rw [h2] at h3
      exact h3

end GlobalTheory.HalfInt

end
end

