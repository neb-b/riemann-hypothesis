module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0464
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0344
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsValueFixedLevelPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0475
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffFourierJacob
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepSupp

variable {D : D7}

theorem mem_cong {V : HSp D} {I : Ideal (AE D)} {g : GA D V}
    (h : ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I) : g ∈ congGrp V I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  ext i j
  have := h i j
  rw [← Ideal.Quotient.eq] at this
  simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
  exact this

theorem off_union {V : HSp D} {P P' R : Pl D → Prop} (hR : ∀ p, R p → P p ∨ P' p) {g : GA D V} (h : g ∈ grpOff V P)
    (h' : g ∈ grpOff V P') : g ∈ grpOff V R := by
  refine mem_cong fun i j => ?_
  have a := GlobalTheory.DisjComb.mem_congGrp' h i j
  have b := GlobalTheory.DisjComb.mem_congGrp' h' i j
  unfold idOff at a b ⊢
  simp only [Submodule.mem_iInf] at a b ⊢
  intro u
  rcases hR u.1 u.2 with k | k
  · exact a ⟨u.1, k⟩
  · exact b ⟨u.1, k⟩

theorem at_le_off (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → ¬ P' p) : grpAt V P ≤ grpOff V P' :=
  (_root_.GlobalTheory.FinPl.SetCut.grp_split D V ∅).2.2.2.2.2.2.1 P P' h

theorem at_eq (V : HSp D) (P : Pl D → Prop) : grpAt V P = GfC V ⊓ grpOff V (fun p => ¬ P p) := by
  rw [(_root_.GlobalTheory.FinPl.SetCut.grp_split D V ∅).2.2.2.2.2.2.2.1]
  simp only [not_not]

theorem at_le_fin (V : HSp D) (P : Pl D → Prop) : grpAt V P ≤ GfC V := by
  rw [at_eq]; exact inf_le_left

theorem at_mono (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : grpAt V P ≤ grpAt V P' := by
  rw [at_eq V P']
  exact le_inf (at_le_fin V P) (at_le_off V fun p hp hn => hn (h p hp))

theorem split_two (V : HSp D) (A B : Finset (Pl D)) {x : GA D V} (hx : x ∈ GfC V)
    (ho : x ∈ grpOff V (fun p => p ∉ A ∧ p ∉ B)) :
    ∃ a ∈ grpAt V (· ∈ A), ∃ b ∈ grpAt V (· ∈ B), b ∈ grpAt V (· ∉ A) ∧ x = a * b := by
  obtain ⟨e, he⟩ := (_root_.GlobalTheory.FinPl.SetCut.grp_split D V A).2.2.2.2.2.1
  obtain ⟨⟨a, b⟩, hab⟩ := e.surjective ⟨x, hx⟩
  have h1 : x = a.1 * b.1 := by
    have := he (a, b)
    rw [hab] at this
    exact this
  refine ⟨a.1, a.2, b.1, ?_, b.2, h1⟩
  rw [at_eq]
  refine ⟨at_le_fin V _ b.2, ?_⟩
  have hb1 : b.1 ∈ grpOff V (fun p => p ∉ A ∧ p ∉ B) := by
    have : b.1 = a.1⁻¹ * x := by rw [h1]; group
    rw [this]
    exact mul_mem (inv_mem (at_le_off V (fun p hp hn => hn.1 hp) a.2)) ho
  have hb2 : b.1 ∈ grpOff V (· ∈ A) := at_le_off V (fun p hp hn => hp hn) b.2
  refine off_union (fun p hp => ?_) hb1 hb2
  by_cases h : p ∈ A
  · exact Or.inr h
  · exact Or.inl ⟨h, hp⟩

theorem vac_om {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT P f) {g : GA D S} {h : GA D T} (hg : g ∈ grpOff S P) (hh : h ∈ grpOff T P) :
    Vac ψ S T LS LT P (om (g, h) f) := by
  have key : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) P, heisO ψ S T u f = f →
      heisO ψ S T u (om (g, h) f) = om (g, h) f := by
    intro u hu e
    have := hW.om_heis g h u f hf.1
    rw [GlobalTheory.DisjComb.actO_off hg hh (GlobalTheory.FinPl.LatMem.latO_mxAt hu), e] at this
    exact this.symm
  refine ⟨hW.om_pres _ _ hf.1, fun u hu => key _ (AddSubgroup.nsmul_mem _ hu 2) (hf.2.1 u hu),
    fun e he u hu hh' => key u hu (hf.2.2 e he u hu hh')⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P Q : Pl D → Prop}
    (hQ : ∀ p, Q p → P p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT Q f := by
  have hm : latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) P := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (hQ v hq), rest⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hm hu), fun e he u hu => hf.2.2 e he u (hm hu)⟩

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ q₁ ∈ GfC (c.V (j + 1)), ∀ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∃ κ, InK (c.V (j + 1)) (v.N (j + 1)) (offP v w) κ ∧ ∃ k ∈ v.JG (j + 1), q₁ = r * y * (κ * k) := by
  intro D c v t w hc hv ht hf _ hoff hG _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ _ G x a _ f _ q₁ hq₁ q₂ hne
  have DC := GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1))
  have hom := (ht.sBF j (σ + 1) h).1
  have hW : IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) (t.sBF j (σ + 1) h).χV (t.sBF j (σ + 1) h).χW (t.om j) := by
    rw [← hom]; exact (t.sBF j (σ + 1) h).weil
  have hGQ : ∀ p, p ∈ w.Q → p ∉ v.gP := fun p hp => Finset.disjoint_left.1 hf.disjG hp

  obtain ⟨g, hg, hflat⟩ : ∃ g ∈ grpAt (c.V j) (· ∈ w.Q), flatBF (t.sBF j (σ + 1) h)
      (t.om j (g, q₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁))) ≠ 0 := by
    unfold integ at hne
    obtain ⟨α, -, hα⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨g, hg, hg'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
    refine ⟨g, (hf.e j α).2 g hg, fun h0 => hg' ?_⟩
    rw [← hom] at h0
    have H := GlobalTheory.HandHom.hand_hom D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (φ α)
    unfold Chain.hand
    erw [h0, H.2.1]
    have := H.2.2 0 1 0 (rTrans q₂ f)
    rw [zero_smul, one_smul, zero_mul, zero_mul] at this
    erw [this, mul_zero]

  have vQ : ∀ P : Pl D → Prop, (∀ p, p ∈ w.Q → ¬ P p) →
      Vac c.ψ _ _ (v.N j) (v.N (j + 1)) P (comb c.ψ _ _ (w.eQ j) Ψ₁) := fun P hP =>
    ((DC (· ∈ w.Q) P hP).2.1 (w.eQ j) (hf.atQ j).1).2 _ _ _ (vac_mono (fun _ _ => trivial) h₁)
  have k₁ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (offP v w) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) :=
    ((DC (· ∈ v.gP) (offP v w) (fun p hp hn => hn.1 hp)).2.1 (v.eG j) (hv.atG j).1).2 _ _ _
      (vQ _ fun p hp hn => hn.2 hp)
  have k₂ : ∀ P, Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) P Ψ₂ := fun P => vac_mono (fun _ _ => trivial) h₂
  have k₁' := vac_om hW k₁ (at_le_off _ (fun p hp hn => hn.2 hp) hg) (one_mem (grpOff (c.V (j + 1)) (offP v w)))
  have mulom : ∀ (g₁ g₂ : GA D (c.V j)) (y₁ y₂ : GA D (c.V (j + 1))) (Φ : WO (c.V j) (c.V (j + 1)) → ℂ),
      t.om j (g₁ * g₂, y₁ * y₂) Φ = t.om j (g₁, y₁) (t.om j (g₂, y₂) Φ) := by
    intro g₁ g₂ y₁ y₂ Φ
    rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]
  obtain ⟨r, hr, hrP, z, hz, κ, hκ, hdec⟩ := (hoff j σ h _ _ k₁' (k₂ _)).2.2.1 q₁ (by
    rw [← mulom, one_mul, mul_one]; exact hflat)
  have hzf : z ∈ GfC (c.V (j + 1)) := by
    have : z = r⁻¹ * q₁ * κ⁻¹ := by rw [hdec]; group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (at_le_fin _ _ hrP)) hq₁) (inv_mem (at_le_fin _ _ hκ.1))
  obtain ⟨s, hs, y, hy, hy', hzs⟩ := split_two (c.V (j + 1)) v.gP w.Q hzf hz

  have e₁ := ((hoff j σ h _ _ k₁ (k₂ _)).1 κ hκ).1
  have hgo : g ∈ grpOff (c.V j) (· ∈ v.gP) := at_le_off _ hGQ hg
  have hyo : y ∈ grpOff (c.V (j + 1)) (· ∈ v.gP) := at_le_off _ hGQ hy
  have vG := vQ (· ∈ v.gP) hGQ
  have e₂ := (DC (· ∈ v.gP) (fun _ => False) (fun _ _ => id)).2.2.1 _ _ _ hW (v.eG j) (hv.atG j).1 g hgo y hyo _ vG.1
  have e₃ : t.om j (g, q₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) =
      t.om j (1, r) (t.om j (1, s) (comb c.ψ _ _ (v.eG j) (t.om j (g, y) (comb c.ψ _ _ (w.eQ j) Ψ₁)))) := by
    rw [← e₂]
    conv_rhs => rw [← e₁]
    rw [← mulom, ← mulom, ← mulom, hdec, hzs]
    simp only [one_mul, mul_one, mul_assoc]
  have th : IsThetaFunO c.ψ _ _ (t.om j (1, s) (comb c.ψ _ _ (v.eG j) (t.om j (g, y) (comb c.ψ _ _ (w.eQ j) Ψ₁)))) := by
    rw [← e₂]
    exact hW.om_pres _ _ (hW.om_pres _ _ k₁.1)
  have hfl : flatBF (t.sBF j (σ + 1) h)
      (t.om j (1, s) (comb c.ψ _ _ (v.eG j) (t.om j (g, y) (comb c.ψ _ _ (w.eQ j) Ψ₁)))) ≠ 0 := by
    intro h0
    apply hflat
    have := ((_root_.GlobalTheory.FlatRInv.vanish_invariant D c.ψ (offP v w)).1 _ _ _ (t.sBF j (σ + 1) h) _ th r hr hrP).2 h0
    rw [hom] at this
    rw [e₃]
    exact this
  obtain ⟨r', hr', hr'P, k, hk, hsk⟩ := (hG j σ h _ _ (vac_om hW vG hgo hyo) (k₂ _)).1 s hs hfl
  refine ⟨r * r', mul_mem hr hr', mul_mem (at_le_fin _ _ hrP) (at_le_fin _ _ hr'P), y, hy, κ, hκ, k, hk, ?_⟩
  have hkP : k ∈ grpAt (c.V (j + 1)) (· ∈ v.gP) := (hv.JG (j + 1) (by omega)).1 hk
  have hcm := (_root_.GlobalTheory.FinPl.SetCut.grp_split D (c.V (j + 1)) v.gP).2.2.2.2.1 k hkP (y * κ)
    (mul_mem hy' (at_mono _ (fun p hp => hp.1) hκ.1))
  rw [hdec, hzs, hsk]
  calc r * (r' * k * y) * κ = r * r' * (k * (y * κ)) := by group
    _ = r * r' * y * (κ * k) := by rw [hcm]; group

end GlobalTheory.DStepSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedVacuaOfShapeProof
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

namespace GlobalTheory.SeeSaw.VacShape

theorem nonempty_pl (D : D7) : Nonempty (Pl D) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField D.host.F)⟩⟩

theorem vacOfShape : ∀ D : D7, GlobalTheory.SeeSaw.VacOfShape D := by
  intro D c v k _ _ _ _ ι o hc hv hs t
  obtain ⟨x₀⟩ := nonempty_pl D
  have hFV := _root_.GlobalTheory.FinPl.FlatVacuum.flatVac D c.ψ (· ∉ v.tP)
  have hCC := _root_.GlobalTheory.ContrComb.contr_comb_main D c.ψ hc.std
  refine ⟨?_, ?_⟩
  · intro j σ h Ψ₁ Ψ₂ h₁ h₂
    have f₁ := hFV.1 (σ + 1) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (t.sBF j (σ + 1) h) (v.N j) (o.M j (σ + 1) h)
      (v.N (j + 1)) (c.x (j + 1)).L (fun x _ => (hs.good x).bf j (σ + 1) h) Ψ₁ h₁
    have f₂ := hFV.2.1 σ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sFB j σ h) (v.N (j + 1)) (c.x (j + 1)).L
      (v.N (j + 1 + 1)) (o.M (j + 1 + 1) σ (idx_step h)) (fun x _ => (hs.good x).fb j σ h) Ψ₂ h₂
    have hg0 := (hs.good x₀).bf j (σ + 1) h
    have hg1 := (hs.good x₀).fb j σ h
    have hor : ∀ x, x ∉ v.tP → (∃ LL, OrthAt (c.B j (σ + 1) h).o (o.M j (σ + 1) h) (c.x j).L LL x) ∧
        ∃ LL, OrthAt (c.B (j + 1 + 1) σ (idx_step h)).o (o.M (j + 1 + 1) σ (idx_step h)) (c.x (j + 1 + 1)).L LL x := by
      intro x hx
      obtain ⟨LL, _, hLL⟩ := (hs.split x hx).core j (σ + 1) h
      obtain ⟨LL', _, hLL'⟩ := (hs.split x hx).core (j + 1 + 1) σ (idx_step h)
      exact ⟨⟨LL, hLL⟩, ⟨LL', hLL'⟩⟩
    exact (hCC (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h)
      _ _ f₁.1 f₂.1).2.2 (· ∉ v.tP) (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (o.M j (σ + 1) h)
      (o.M (j + 1 + 1) σ (idx_step h)) (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd hg0.sdV₀ hg1.sdW₀ hor f₁ f₂
  · intro j h Ψ₁ Ψ₂ h₁ h₂
    have f₁ := hFV.1 0 (c.B j 0 h) (c.J j 0 h) (t.sBF j 0 h) (v.N j) (o.M j 0 h) (v.N (j + 1)) (c.x (j + 1)).L
      (fun x _ => (hs.good x).bf j 0 h) Ψ₁ h₁
    have f₂ := hFV.2.2 (c.V (j + 1)) (c.X (j + 1)) c.T (c.jac j 0 h).d (v.N (j + 1)) (c.x (j + 1)).L v.NT
      (hv.sd (j + 1) (by omega)) (hc.x (j + 1) (by omega)).sd hv.sdT (fun x _ => ((hs.good x).bf j 0 h).monoW) Ψ₂ h₂
    have hg0 := (hs.good x₀).bf j 0 h
    exact _root_.GlobalTheory.LastVacPf.lastVac D c.ψ hc.std _ (c.X j) _ (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz (c.bes j 0 h).o
      (c.oT (j + 1 + 1) h) (v.τ j h) (c.bes j 0 h).line.1 hs.pre.line.1 (hs.pre.tau j h) (· ∉ v.tP) (o.M j 0 h)
      (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L v.NT hg0.sdV₀ (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd hv.sdT (fun x hx => ⟨((hs.good x).bf j 0 h).tame, (hs.split x hx).top j h⟩)
      _ _ f₁ f₂

end GlobalTheory.SeeSaw.VacShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedValueCommonConstantsFixedLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.GValAll

theorem gValue_common : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∃ a : ℕ → ℂ, (∀ j, a j ≠ 0) ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → GValue (t := t) (v.withCG a) := by
  intro D c v n G hc hv hG
  classical
  refine ⟨fun j => if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then (_root_.GlobalTheory.SeeSaw.GValMid.gValue_mid D c v n G hc hv hG j h1.choose h1.choose_spec).choose
    else if h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧
      (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram then
      (_root_.GlobalTheory.LevelLast.last_value D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose else 1, ?_, ?_⟩
  · intro j
    dsimp only
    by_cases h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m
    · rw [dite_eq_left h1]; exact (_root_.GlobalTheory.SeeSaw.GValMid.gValue_mid D c v n G hc hv hG j h1.choose h1.choose_spec).choose_spec.1
    · rw [dite_eq_right h1]
      by_cases h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧
          (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram
      · rw [dite_eq_left h2]; exact (_root_.GlobalTheory.LevelLast.last_value D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose_spec.1
      · rw [dite_eq_right h2]; exact one_ne_zero
  · intro t _ hw
    refine ⟨fun j σ h Ψ₁ Ψ₂ h₁ h₂ => ?_, fun j h Ψ₁ Ψ₂ h₁ h₂ => ?_⟩
    · have h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m := ⟨σ, h⟩
      have hσ : h1.choose = σ := by have := h1.choose_spec; omega
      show _ = (if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then _ else _) • _
      rw [dite_eq_left h1]
      have key := (_root_.GlobalTheory.SeeSaw.GValMid.gValue_mid D c v n G hc hv hG j h1.choose h1.choose_spec).choose_spec.2
      revert key
      generalize (_root_.GlobalTheory.SeeSaw.GValMid.gValue_mid D c v n G hc hv hG j h1.choose h1.choose_spec).choose = C
      intro key
      subst hσ
      exact key _ _ Ψ₁ Ψ₂ h₁ h₂
    · have h1 : ¬ ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m := by rintro ⟨σ, hσ⟩; omega
      obtain ⟨hr, hτ⟩ := hw.tau j h
      have h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧
          (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram := ⟨h, hr, hτ⟩
      show _ = (if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then _ else _) • _
      rw [dite_eq_right h1, dite_eq_left h2]
      exact (_root_.GlobalTheory.LevelLast.last_value D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose_spec.2 _ Ψ₁ Ψ₂ h₁ h₂

end GlobalTheory.SeeSaw.GValAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAllGluedPlacesProof
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SmallAllPf

variable {D : D7}

theorem vac_at_place {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop}
    {f : WO S T → ℂ} (h : Vac ψ S T LS LT P f) {v : Pl D} (hv : P v) : Vac ψ S T LS LT (· = v) f := by
  have hle : latO S T (LS : Set _) (LT : Set _) (· = v) ≤ latO S T (LS : Set _) (LT : Set _) P := by
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨α, hα, hP, rest⟩
    exact ⟨α, hα, fun w hw => hP w fun e => hw (e ▸ hv), rest⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem main : ∀ D : D7, GlobalTheory.FinPl.SmallAll D := by
  intro D k _ _ _ _ ι p I P hP n n' _ _ _ _ q χ hχ
  have hSO := _root_.GlobalTheory.FinPl.smallOne D
  have hOB := _root_.GlobalTheory.FinPl.overBasic D
  have hAB := _root_.GlobalTheory.FinPl.allBijective_all D
  choose r e hr hval using fun i => hSO k (p i) n n' q (χ i) (hχ i)
  refine ⟨r, e, hr, ?_⟩
  intro ψ V₀ A L S T o ζ hζ hA hS hT χV χW χS χT om₁ omT hom₁ homT hunr vA vS vT a b s L₁ L₂ L₃ hL₁ hL₂ hL₃ hloc
    Ξ Ξ' Φ₂ hΞ hΦ₂ hO φ hφ F hF
  have hstd : IsStdChar D ψ (-1) := hom₁.std
  have hinj : Function.Injective fun i => (p i).v := hP.inj
  have hPi : ∀ i, P (p i).v := fun i => (hP.mem _).2 ⟨i, rfl⟩
  set c : ι → ℂ := fun i => (r i : ℂ) * chrPow χW ((p i).idele q.unit) (e i) with hc
  set Ψ : ι → Matrix n (n' ⊕ Fin 1) k → ℂ :=
    fun i => tensCol (phiOne (a.P i) (b.Q i)) (charInd (resChar (χ i) (hχ i) q) (s i • b.Q i)) with hΨ

  have keep : ∀ (l : List ι) (f f' : WO V₀ S → ℂ),
      OverAll ψ a.α₀ b.β L₁ L₂ Ψ l f f' → ∀ i, i ∉ l → Vac ψ V₀ S L₁ L₂ (· = (p i).v) f →
        Vac ψ V₀ S L₁ L₂ (· = (p i).v) f' := by
    intro l
    induction l with
    | nil =>
      intro f f' h i _ hv
      have h' : f' = f := h
      rw [h']
      exact hv
    | cons j l ih =>
      intro f f' h i hi hv
      obtain ⟨g, hg, hOj⟩ := h
      have hgv := ih f g hg i (fun hm => hi (List.mem_cons_of_mem j hm)) hv
      have hij : i ≠ j := fun e => hi (e ▸ List.mem_cons_self)
      exact ((hOB k (p j) n (n' ⊕ Fin 1) ψ hstd V₀ S (a.α₀ j) (b.β j) L₁ L₂ hL₁ hL₂ g hOj.2.2.1).2.1 _ _
        hOj).2 L₁ L₂ _ (fun e => hij (hinj e).symm) hgv
  have val : ∀ l : List ι, l.Nodup → ∀ (Ξ₀ Ξ₁ : WO V₀ S → ℂ),
      (∀ i, Vac ψ V₀ S L₁ L₂ (· = (p i).v) Ξ₀) → OverAll ψ a.α₀ b.β L₁ L₂ Ψ l Ξ₀ Ξ₁ →
      ∀ φ, a.Ram φ → smallPair o om₁ omT vA vS vT φ Ξ₀ Φ₂ F =
        (l.map c).prod * smallPair o om₁ omT vA vS vT (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ) Ξ₁ Φ₂ F := by
    intro l
    induction l with
    | nil =>
      intro _ Ξ₀ Ξ₁ _ h φ _
      have h' : Ξ₁ = Ξ₀ := h
      subst h'
      simp [PairDat.sAll]
    | cons j l ih =>
      intro hnd Ξ₀ Ξ₁ h1 h φ hφ
      obtain ⟨g, hg, hOj⟩ := h
      have hj : j ∉ l := (List.nodup_cons.1 hnd).1
      have hgv := keep l Ξ₀ g hg j hj (h1 j)
      rw [ih hnd.tail Ξ₀ g h1 hg φ hφ]
      have hR : a.Ram (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ) :=
        (hAB k ι p q χ hχ s n' A V₀ a hinj l).1.mapsTo hφ
      have hself := (hOB k (p j) n (n' ⊕ Fin 1) ψ hstd V₀ S (a.α₀ j) (b.β j) L₁ L₂ hL₁ hL₂ g hgv).2.2
        (hP.unit j) _ _ (hloc j).2.1 (hloc j).2.2
      obtain ⟨u1, u2, u3, u4⟩ := hunr _ (hPi j)
      have key := hval j ψ V₀ A L S T o ζ hζ hA hS hT χV χW χS χT om₁ omT hom₁ homT u1 u2 u3 u4 vA vS vT
        (a.α j) (a.α₀ j) (b.β j) (hloc j).1 (a.P j) (b.Q j) (s j) L₁ L₂ L₂ L₃ g g Ξ₁ Φ₂ hself hOj hL₂ hL₃
        (hloc j).2.2 (vac_at_place hΦ₂ (hPi j)) _ (hR.2 j) F hF
      have hcons : a.sAll q (fun i => resChar (χ i) (hχ i) q) s (j :: l) φ =
          sOp (a.α j) (a.P j) q (resChar (χ j) (hχ j) q) (s j)
            (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ) := rfl
      rw [key, hcons, List.map_cons, List.prod_cons, hc]
      ring
  exact val I hP.nodup Ξ Ξ' (fun i => vac_at_place hΞ (hPi i)) hO φ hφ

end GlobalTheory.FinPl.SmallAllPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroRepresentativeDiffersByLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZero_representative_differs_by_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ c : {c // A.chOf 0 c = β}, ∃ κ : (A.K 0 (Nat.zero_le _) β).lev.U, ((C.forms u).to0.cls0.y ((I.eCls0 l u a).symm c.1)).1 = ((A.K 0 (Nat.zero_le _) β).y c).1 * κ.1 ∧ (A.K 0 (Nat.zero_le _) β).lev.chi κ = 1 := by
  first | exact @GlobalTheory.Fam.rep_zero_std | exact GlobalTheory.Fam.rep_zero_std | (intros; apply GlobalTheory.Fam.rep_zero_std <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsRealDataSpecStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumns_realData_spec : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) → (realOf u R g s J).Is := by
  first | exact @GlobalTheory.AdForm.realOf_is | exact GlobalTheory.AdForm.realOf_is | (intros; apply GlobalTheory.AdForm.realOf_is <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

namespace GlobalTheory.TopVol.TwistPlaces

theorem sel_under {X : Formalism.L2.Col.Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    (hsel : Formalism.L2.Col.IsSel X sel) {ξ : Formalism.L2.DIV.Chr X.F X.E X.K} {P : HeightOneSpectrum (𝓞 X.E)}
    (h : P ∈ Formalism.L2.Col.QE sel ξ) : sel (P.under (𝓞 X.F)) = P := by
  unfold Formalism.L2.Col.QE at h
  split_ifs at h with hf
  · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 h
    have e : (sel v).under (𝓞 X.F) = v := HeightOneSpectrum.ext (hsel v)
    rw [e]
  · exact absurd h (Finset.notMem_empty _)

end GlobalTheory.TopVol.TwistPlaces
end

