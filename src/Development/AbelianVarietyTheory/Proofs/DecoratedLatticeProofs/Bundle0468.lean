module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0249
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineMultipleMemSplitCoreLatticeCompletionIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LineIdeal

theorem e_half : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : Submodule 𝒪[k] (n → k)), IsSumFrame o ζ α α₀ → α₀.IsLat M (lastKer Λ) → ∀ c : AE D, ((fun r => p.e * (c * incA D (vecB o ζ r))) ∈ latV S₀ M (· = p.v) ↔ p.pr c ∈ 𝒪[k]) := by

  intro D k _ _ _ _ p n _ _ S₀ A L o ζ α α₀ M Λ hsum hlat c
  have key : (fun r => p.e * (c * incA D (vecB o ζ r))) =
      fun r => p.sec ((α₀.b *ᵥ Pi.single (Sum.inr 0) (p.pr c)) r) := by
    funext r
    have hb : α₀.b r (Sum.inr 0) = p.pr (incA D (vecB o ζ r)) := by
      rw [hsum]; rfl
    have hv : (α₀.b *ᵥ Pi.single (Sum.inr 0) (p.pr c)) r = α₀.b r (Sum.inr 0) * p.pr c := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv, hb, ← map_mul, p.sec_pr, mul_comm (incA D _) c]
  rw [key, ← hlat, GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
  have h1 : (Pi.single (Sum.inr 0) (p.pr c) : n ⊕ Fin 1 → k) ∘ Sum.inl = 0 := by
    funext j; simp
  simp [h1]

theorem mem_latV_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ c : AE D, c ∈ idAt D P → ((fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M P ↔ (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) ∈ 𝒪[k])) := by

  intro D k _ _ _ _ ι p I P hP n _ _ S₀ A L o ζ hζ α α₀ M Λ hM hfr c hc
  have hyid : ∀ r, (fun r => c * incA D (vecB o ζ r)) r ∈ idAt D P := fun r => Ideal.mul_mem_right _ _ hc
  have hloc : (fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M P ↔ ∀ i,
      GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M (· = (p i).v) := by
    constructor
    · intro h i
      exact GlobalTheory.FinPlLoc.smul_latV _ (GlobalTheory.FinPlLoc.idem_mem_intAt _) h
    · intro h
      refine (GlobalTheory.FinPlLoc.part_lat P S₀ M _ hM.1).2 ⟨hyid, fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := (hP.mem v).1 hv
      have h1 : e • (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) =
          e • (fun r => c * incA D (vecB o ζ r)) := by
        rw [smul_smul, mul_comm, (GlobalTheory.FinPlLoc.mem_idAt_iff _ e).1 he.1]
      rw [← h1]
      exact GlobalTheory.FinPlLoc.smul_latV _ he (h i)
  rw [hloc]
  refine forall_congr' fun i => ?_
  have hεid : ∀ r, (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) r ∈ idAt D (· = (p i).v) :=
    fun r => Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_intAt _).1
  rw [GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts D k (p i) S₀ M _ hεid]
  have he : GlobalTheory.FinPlLoc.idem D (· = (p i).v) * (p i).e = (p i).e :=
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (FrameLat.e_mem_idAt (p i))
  have hce_id : cA D (p i).e ∈ idAt D (· = (p i).v) := by
    have := Ideal.sub_mem _ (FrameLat.sum_mem_idAt (p i)) (FrameLat.e_mem_idAt (p i))
    rwa [add_sub_cancel_left] at this
  have hce : GlobalTheory.FinPlLoc.idem D (· = (p i).v) * cA D (p i).e = cA D (p i).e :=
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 hce_id
  have e1 : (fun r => (p i).e * (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) r) =
      fun r => (p i).e * (c * incA D (vecB o ζ r)) := by
    funext r
    rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (p i).e, he]
  have e2 : (fun r => cA D (p i).e * (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) r) =
      fun r => cA D (p i).e * (c * incA D (vecB o ζ r)) := by
    funext r
    rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (cA D (p i).e), hce]
  rw [e1, e2, e_half D k (p i) n S₀ A L o ζ (α i) (α₀ i) M (Λ i) (hfr i).1 (hfr i).2 c,
    _root_.GlobalTheory.FinPl.ConjHalf.conj_half D k (p i) n S₀ A L o ζ (α i) (α₀ i) M (Λ i) hM (hfr i).1 (hfr i).2 c]

end GlobalTheory.LineIdeal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineVectorPairingMemInverseIdealCompletion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.LineDual

variable {D : D7}

theorem intAt_zero' (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩

theorem intAt_add' {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg' {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem latV_entry_mem_idAt {S : HSp D} {M : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S M P) (i : Fin S.rank) : y i ∈ idAt D P := by
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, x, -, rfl⟩ := hw
    exact LatMem.tmul_mem_idAt hα _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem idV_mem_idAt {𝔞 : FI D} {v : Pl D} {t : AE D} (ht : t ∈ idV 𝔞 v) : t ∈ idAt D (· = v) := by
  induction ht using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, rfl⟩ := hw
    exact LatMem.tmul_mem_idAt (fun w hw => hα w hw) _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem cA_mem_idAt {v : Pl D} {a : AE D} (h : a ∈ idAt D (· = v)) : cA D a ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

def pr (S : HSp D) (w y : Fin S.rank → AE D) : AE D := ∑ l, (∑ m, cA D (w m) * gA S m l) * y l

theorem pr_zero_left (S : HSp D) (y : Fin S.rank → AE D) : pr S 0 y = 0 := by simp [pr]
theorem pr_zero_right (S : HSp D) (w : Fin S.rank → AE D) : pr S w 0 = 0 := by simp [pr]
theorem pr_add_left (S : HSp D) (w w' y : Fin S.rank → AE D) : pr S (w + w') y = pr S w y + pr S w' y := by
  simp [pr, add_mul, Finset.sum_add_distrib]
theorem pr_add_right (S : HSp D) (w y y' : Fin S.rank → AE D) : pr S w (y + y') = pr S w y + pr S w y' := by
  simp [pr, mul_add, Finset.sum_add_distrib]
theorem pr_neg_left (S : HSp D) (w y : Fin S.rank → AE D) : pr S (-w) y = -pr S w y := by
  simp [pr]
theorem pr_neg_right (S : HSp D) (w y : Fin S.rank → AE D) : pr S w (-y) = -pr S w y := by
  simp [pr]

theorem pr_gen (S : HSp D) (α β : Af D.host.F) (x x' : Fin S.rank → D.host.E) :
    pr S (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
      pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (∑ m, ∑ l, star (x m) * S.gram m l * x' l) := by
  have hc : ∀ m, cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x m) = pairA D.host.F 0 α ⊗ₜ[D.host.F] star (x m) :=
    fun _ => rfl
  have hg : ∀ m l, gA S m l = (1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram m l := fun _ _ => rfl
  have hp : pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := Prod.ext (zero_mul _) rfl
  simp only [pr, one_mul]
  simp only [hc, hg, Finset.sum_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]
  rw [Finset.sum_comm]
  simp only [← TensorProduct.tmul_sum]

theorem pr_mem_intAt {S : HSp D} {M : Lat S} (hM : IsSelfDualC S M) {P : Pl D → Prop} {w y : Fin S.rank → AE D}
    (hw : w ∈ latV S M P) (hy : y ∈ latV S M P) : pr S w y ∈ intAt D P := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hw
    rw [Set.mem_singleton_iff] at ha
    subst ha
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨β, hβi, hβ, c, hc, x', hx', rfl⟩ := hz
      rw [Set.mem_singleton_iff] at hc
      subst hc
      rw [pr_gen]
      obtain ⟨b, hb⟩ := (hM.2 x').1 hx' x hx
      refine ⟨LatMem.tmul_mem_idAt (fun v hv => by rw [map_mul, hα v hv, zero_mul]) _, ?_⟩
      rw [← hb]
      exact AddSubgroup.subset_closure ⟨α * β, LatMem.intAf_mul' hαi hβi, b, rfl⟩
    | zero => rw [pr_zero_right]; exact intAt_zero' _
    | add z z' _ _ hz hz' => rw [pr_add_right]; exact intAt_add' hz hz'
    | neg z _ hz => rw [pr_neg_right]; exact intAt_neg' hz
  | zero => rw [pr_zero_left]; exact intAt_zero' _
  | add w w' _ _ hw hw' => rw [pr_add_left]; exact intAt_add' hw hw'
  | neg w _ hw => rw [pr_neg_left]; exact intAt_neg' hw

theorem line_pair_mem_idV : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L : HSp D) (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D), IsSelfDualC S M → LineId o ζ M 𝔠 v → 𝔠 ≠ 0 →
      ∀ y ∈ latV S M (· = v), cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idV 𝔠⁻¹ v := by
  intro D ψ hψ S A L o ζ M 𝔠 v hM hline h𝔠 y hy
  obtain ⟨h1, h2, -, h4, -⟩ := GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hX : (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idAt D (· = v) :=
    sum_mem fun l _ => Ideal.mul_mem_left _ _ (latV_entry_mem_idAt hy l)
  have hcX := cA_mem_idAt hX
  have hcint : ∀ s, s ∈ intAt D (· = v) → cA D s ∈ intAt D (· = v) := by
    intro s hs
    have e2 : s ∈ idV (D.host.AA ^ (0 : ℤ)) v := by rw [zpow_zero]; exact (h1 s).2 hs
    have e3 := (h4 0 s).1 e2
    rw [zpow_zero] at e3
    exact (h1 _).1 e3
  have key := (h2 𝔠 1 h𝔠 one_ne_zero _ hcX).1 (fun t ht => ?_)
  · rwa [one_mul] at key
  · have htI : t ∈ idAt D (· = v) := idV_mem_idAt ht
    have htz : t • ratV (vecB o ζ) ∈ latV S M (· = v) := (hline t htI).2 ht
    have hp := pr_mem_intAt hM htz hy
    have he : pr S (t • ratV (vecB o ζ)) y = cA D t * ∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l := by
      simp only [pr, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [he] at hp
    have h5 := hcint _ hp
    rw [map_mul, Formalism.L2.Theta.cA_cA, mul_comm] at h5
    exact (h1 _).2 h5

end GlobalTheory.LineDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentAtSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QGeoAt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

noncomputable def glOf (p : Place D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) :
    GL Y k →* GA D S where
  toFun gk := Classical.choose (((GlobalTheory.LocGrp.local_groups D k p).1 S Y F).1 gk)
  map_one' := by
    have h := ((GlobalTheory.LocGrp.local_groups D k p).1 S Y F)
    set g0 := Classical.choose (h.1 1)
    have h0 : p.IsLoc F g0 1 := (Classical.choose_spec (h.1 1)).1
    have h00 : p.IsLoc F (g0 * g0) 1 := by simpa using h.2.2 _ _ _ _ h0 h0
    have e := (Classical.choose_spec (h.1 1)).2 _ h00
    exact mul_left_cancel (a := g0) (by rw [mul_one]; exact e)
  map_mul' a b := by
    have h := ((GlobalTheory.LocGrp.local_groups D k p).1 S Y F)
    have ha := (Classical.choose_spec (h.1 a)).1
    have hb := (Classical.choose_spec (h.1 b)).1
    exact ((Classical.choose_spec (h.1 (a * b))).2 _ (h.2.2 _ _ _ _ ha hb)).symm

theorem glOf_loc (p : Place D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (g : GL Y k) :
    p.IsLoc F (glOf p S F g) g :=
  (Classical.choose_spec (((GlobalTheory.LocGrp.local_groups D k p).1 S Y F).1 g)).1

end GlobalTheory.QGeoAt


open GlobalTheory.QGeoAt in
theorem GlobalTheory.QGeoAt.geo_of_frames : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → ∀ (PP : Pl D.host.E), QAll W PP → ∀ (l : LocX a (pk W).βX PP), LocY l y v.N (pk W).βY b (fun _ _ _ => 1) → (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (l.FX j hj)) → IsStdFr GlobalTheory.SymBridge.zPos l.FT → ∃ G : GlobalTheory.QTw.QGeo v (baseOf (pk W) (lvP W) u (mkGeo m b)) PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (G.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos G.FT ∧ G.z₀ = fun r => (ofSplit G.q).pr (a.ζ₀ r) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b v hv hτ hNT PP hPP l hY hFX hFT
  obtain ⟨⟨ψk, hchar, hcond⟩, ⟨ν, hν⟩, hϖ⟩ := _root_.GlobalTheory.WeilCondUnif.cond_unif W u hW a PP (Or.inr hPP) l
  obtain ⟨ϖ, hunif, hcompl⟩ := hϖ hPP
  refine ⟨{
    k := l.k
    ν := ν
    unitVol := hν
    q := l.q
    idem := l.idem
    unit := l.unit
    ψk := ψk
    char := hchar
    cond := hcond
    ϖ := ϖ
    unif := hunif
    compl := hcompl
    s := l.s
    hs := l.hs
    FX := l.FX
    FT := l.FT
    FM := l.FM
    FY := hY.FY
    sc := hY.sc
    sc_ne := fun j h => by simpa [h] using hY.sc_unit j
    sc_step := hY.sc_step
    bes := hY.bes
    jac := hY.jac
    z₀ := fun r => (ofSplit l.q).pr (a.ζ₀ r)
    last := l.last
    tau := fun h => by rw [hτ]; exact hY.tau h
    latX := l.latX
    latM := l.latM
    latY := hY.latY
    latT := by rw [hNT]; exact l.latT
    gl := fun j d hd => glOf (ofSplit l.q) _ (hY.FY j d hd)
    gl_loc := fun j d hd g => glOf_loc (ofSplit l.q) _ (hY.FY j d hd) g
    frame := fun j d hd => by
      obtain ⟨e, he, hm⟩ := hY.frame j d hd
      refine ⟨e, he, ?_⟩
      simpa using hm
    frameTop := l.frameTop }, hFX, hFT, rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevSIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.TopLevQ.moved_mat {k Z : Type} [Field k] [Fintype Z] [DecidableEq Z] {n : ℕ} (β : Matrix (Fin n) Z k) (γ : Matrix Z (Fin n) k) (hγβ : γ * β = 1) (x : Matrix Z Z k) (e : Z ≃ Fin n) : β * x * γ * β.submatrix id e.symm = β.submatrix id e.symm * x.submatrix e.symm e.symm := by
  rw [Matrix.submatrix_mul_equiv β x id e.symm e.symm, Matrix.mul_assoc (β * x)]
  have h1 : γ * β.submatrix id e.symm = (γ * β).submatrix id e.symm := by
    ext i j; simp [Matrix.mul_apply]
  rw [h1, hγβ]
  ext i j; simp [Matrix.mul_apply, Matrix.one_apply]

theorem GlobalTheory.TopLevQ.suppAt_conj {D : D7} {e : AE D} {V : HSp D} (g b : GA D V) (hg : Formalism.L2.Theta.SuppAt e V g) :
    Formalism.L2.Theta.SuppAt e V (b⁻¹ * g * b) := by
  have hm : ∀ x y : GA D V, Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := fun x y => by
    unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl
  have h1 : Formalism.L2.Theta.mt V b⁻¹ * Formalism.L2.Theta.mt V b = 1 := by
    rw [← hm, inv_mul_cancel]; unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  have key : Formalism.L2.Theta.mt V (b⁻¹ * g * b) - 1 =
      Formalism.L2.Theta.mt V b⁻¹ * (Formalism.L2.Theta.mt V g - 1) * Formalism.L2.Theta.mt V b := by
    rw [hm, hm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have hg' : (e + (cA D) e) • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 := by
    ext i j; exact hg i j
  have h2 : (e + (cA D) e) • (Formalism.L2.Theta.mt V b⁻¹ * (Formalism.L2.Theta.mt V g - 1) * Formalism.L2.Theta.mt V b) =
      Formalism.L2.Theta.mt V b⁻¹ * ((e + (cA D) e) • (Formalism.L2.Theta.mt V g - 1)) * Formalism.L2.Theta.mt V b := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hg'] at h2
  intro i j
  rw [key]
  exact congrFun (congrFun h2 i) j

theorem GlobalTheory.TopLevQ.blk_iff {K : Type} [Field K] [ValuativeRel K] {κ τ s n : ℕ}
    (e : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin n) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e)
    (x : Matrix (GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2)) (GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2)) K) :
    (∀ i j : Fin n, Formalism.L2.DIV.blk2 (κ + (s + 1)) j < Formalism.L2.DIV.blk2 (κ + (s + 1)) i →
      ValuativeRel.valuation K (x (e.symm i) (e.symm j)) < 1) ↔ GlobalTheory.StepData.MaxM x.toBlocks₂₁ := by
  have hlo : ∀ a : Fin κ ⊕ Fin (s + 1), (e (Sum.inl a)).val < κ + (s + 1) := by
    intro a; rw [he]; rcases a with a | a <;> simp [GlobalTheory.SymBridge.zPos] <;> omega
  have hhi : ∀ p : Fin (s + 2) × Fin τ, κ + (s + 1) ≤ (e (Sum.inr p)).val := by
    intro p; rw [he]; simp only [GlobalTheory.SymBridge.zPos]; exact Nat.le_add_right_of_le (Nat.le_add_right _ _)
  constructor
  · intro h p a
    have := h (e (Sum.inr p)) (e (Sum.inl a)) (by
      simp only [Formalism.L2.DIV.blk2, if_pos (hlo a), if_neg (Nat.not_lt.2 (hhi p))]; omega)
    simp only [Equiv.symm_apply_apply] at this
    exact this
  · intro h i j hij
    have hj : j.val < κ + (s + 1) := by
      by_contra hc
      simp only [Formalism.L2.DIV.blk2, if_neg hc] at hij
      split_ifs at hij <;> omega
    have hi : ¬ i.val < κ + (s + 1) := by
      intro hc
      simp only [Formalism.L2.DIV.blk2, if_pos hc, if_pos hj] at hij
      omega
    obtain ⟨p, hp⟩ : ∃ p, e.symm i = Sum.inr p := by
      rcases hi' : e.symm i with a | p
      · exfalso; apply hi; have := hlo a; rw [← hi', Equiv.apply_symm_apply] at this; exact this
      · exact ⟨p, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a, e.symm j = Sum.inl a := by
      rcases hj' : e.symm j with a | p
      · exact ⟨a, rfl⟩
      · exfalso; have := hhi p; rw [← hj', Equiv.apply_symm_apply] at this; omega
    rw [hp, ha]
    exact h p a

theorem GlobalTheory.TopLevQ.mem_levS_iff {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (y : GA D V) :
    y ∈ levS V β L ↔ y ∈ GfC V ∧ ((Lev.finE V y ∈ Formalism.L2.DIV.St β ∧
        (∀ PP' ∈ L.Pg, Formalism.L2.DIV.redFn β PP' (Lev.finE V y) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t)) ∧
        ∀ PP' ∈ L.Q, Formalism.L2.DIV.redFn β PP' (Lev.finE V y) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 L.r)) ∧
        Formalism.L2.DIV.rTup β L (Lev.finE V y) ∈ L.P.H) := by
  show y ∈ GfC V ⊓ Subgroup.comap (Lev.finE V) (Formalism.L2.DIV.lev _ _ β L) ↔ _
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  show _ ∧ (_ ∈ Formalism.L2.DIV.parLev _ _ _ _ ∧ _) ↔ _
  rw [Formalism.L2.DIV.mem_parLev]
  simp only [GlobalTheory.LevSplit.finE_mem_UA, true_and]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyColCh
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.Fam.TopLocFac


open Formalism.IndefR.Lev Formalism.IndefR.Mult in
theorem nonempty_rowCh {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (u : D.what₂.Word)
    (g : Geo D) (hψ : IsStdChar D R.ψ (-1)) (t : T) : Nonempty (RowCh R P u g t) :=
  ⟨{ vP := fun _ => 0, vT := fun _ _ => 0, sBF := fun _ _ _ => (GlobalTheory.Unf.Inhab.nonempty_stepBF hψ _ _).some,
     sFB := fun _ _ _ => (GlobalTheory.Unf.Inhab.nonempty_stepFB hψ _ _).some, io := fun _ => 0, ioT := fun _ _ => 0 }⟩

theorem nonempty_colCh {D : D7} (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) : Nonempty (ColCh u C) :=
  ⟨{ kom := fun _ => 1, Ch := fun _ => Unit, dd := fun _ _ _ => 0, e := fun _ _ => 0, eT := fun _ _ _ => 0,
     Ram := fun _ => Set.univ, S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 1, cK := fun _ => 1, cP := 1 }⟩

end GlobalTheory.Fam.TopLocFac
end
end

