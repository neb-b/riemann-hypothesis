module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0407
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemMulAAOfTrace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Formalism.LocalRingCardinality.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealHermitianSelfDualOfLocalGenerator
section
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

namespace GlobalTheory.FinPl.SelfDualIdeal

variable {D : D7}
open GlobalTheory.FinPlLoc

theorem alg₁ {R : Type} [CommRing R] {u u' w w' e : R} (hU : u' * u = 1) (hC : w' * w = 1) (he : e * e = e)
    (c d h : R) : e * (c * d * h) = u * w * h * (u' * (e * d) * (w' * (e * c))) := by
  calc _ = (u' * u) * (w' * w) * (e * e) * (c * d * h) := by rw [hU, hC, he, one_mul, one_mul]
    _ = _ := by ring

theorem alg₂ {R : Type} [CommRing R] {u u' : R} (hU : u' * u = 1) (w e d h : R) :
    u * w * h * (u' * (e * d)) = d * h * (w * e) := by
  calc _ = (u' * u) * (d * h * (w * e)) := by ring
    _ = _ := by rw [hU, one_mul]

theorem alg₃ {R : Type} [CommRing R] {u u' e : R} (hU : u' * u = 1) (he : e * e = e) (d y : R) :
    e * (d * y) = u' * (e * d) * (y * (u * e)) := by
  calc _ = (u' * u) * (e * e) * (d * y) := by rw [hU, he, one_mul]
    _ = _ := by ring

theorem intAt_mul {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by
    rw [RingHom.map_mul (finPart D) a b]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem cA_mem_intAt {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : cA D a ∈ intAt D (· = v) := by
  refine ⟨?_, (GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 ha.2⟩
  have h := congrArg (cA D) ((mem_idAt_iff _ a).1 ha.1)
  rw [RingHom.map_mul (cA D), cA_idem] at h
  exact (mem_idAt_iff _ _).2 h

theorem idem_mul_incA (P : Pl D → Prop) (y : D.host.E) :
    idem D P * incA D y = pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] y := by
  rw [mul_comm, idem, GlobalTheory.IdVGen.incA_mul_tmul, mul_one]

theorem idem_mul_incA_mem {𝔞 : FI D} {c : D.host.E} (hc : c ∈ 𝔞) (v : Pl D) : idem D (· = v) * incA D c ∈ idV 𝔞 v :=
  AddSubgroup.subset_closure ⟨ePl D (· = v), ePl_int _, fun w hw => by rw [evalV_ePl, if_neg hw], c, hc,
    idem_mul_incA _ c⟩

theorem mul_incA_mem {v : Pl D} {𝔞 : FI D} {y : D.host.E}
    (hy : ∀ c ∈ 𝔞, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y * c) {s : AE D} (hs : s ∈ idV 𝔞 v) :
    incA D y * s ∈ intAt D (· = v) := by
  induction hs using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, h0, c, hc, rfl⟩ := hz
    obtain ⟨b, hb⟩ := hy c hc
    rw [GlobalTheory.IdVGen.incA_mul_tmul, ← hb]
    exact GlobalTheory.IdVGen.gen_mem_intAt hα h0 b
  | zero => rw [mul_zero]; exact GlobalTheory.IdVGen.intAt_zero' v
  | add a b _ _ ha hb => rw [mul_add]; exact GlobalTheory.IdVGen.intAt_add' ha hb
  | neg a _ ha => rw [mul_neg]; exact GlobalTheory.IdVGen.intAt_neg' ha

theorem mul_cA_mem {v : Pl D} {𝔞 : FI D} {y : D.host.E}
    (hy : ∀ c ∈ 𝔞, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y * star c) {s : AE D} (hs : s ∈ idV 𝔞 v) :
    incA D y * cA D s ∈ intAt D (· = v) := by
  induction hs using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, h0, c, hc, rfl⟩ := hz
    obtain ⟨b, hb⟩ := hy c hc
    have e : cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) = pairA D.host.F 0 α ⊗ₜ[D.host.F] star c := rfl
    rw [e, GlobalTheory.IdVGen.incA_mul_tmul, ← hb]
    exact GlobalTheory.IdVGen.gen_mem_intAt hα h0 b
  | zero => rw [RingHom.map_zero, mul_zero]; exact GlobalTheory.IdVGen.intAt_zero' v
  | add a b _ _ ha hb => rw [RingHom.map_add (f := _), mul_add]; exact GlobalTheory.IdVGen.intAt_add' ha hb
  | neg a _ ha => rw [RingHom.map_neg, mul_neg]; exact GlobalTheory.IdVGen.intAt_neg' ha

theorem exists_int_mul (y : D.host.E) : ∃ t : 𝓞 D.host.F, t ≠ 0 ∧ ∃ b : 𝓞 D.host.E,
    (b : D.host.E) = algebraMap D.host.F D.host.E (t : D.host.F) * y := by
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) (Rₘ := ℚ) y
    (Algebra.IsIntegral.isIntegral y)
  refine ⟨((m : ℤ) : 𝓞 D.host.F), Int.cast_ne_zero.2 (nonZeroDivisors.coe_ne_zero m), ⟨m • y, hm⟩, ?_⟩
  change (m : ℤ) • y = _
  simp [zsmul_eq_mul]

theorem one_eq_sum (T : Finset (Pl D)) :
    (1 : Af D.host.F) = ∑ v ∈ T, ePl D (· = v) + ePl D (· ∉ T) := by
  classical
  have key : ∀ w, evalV D.host.F w (1 : Af D.host.F) =
      evalV D.host.F w (∑ v ∈ T, ePl D (· = v) + ePl D (· ∉ T)) := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_one, map_add (f := _), map_sum]
    simp only [evalV_ePl]
    by_cases hw : w ∈ T <;> simp [hw]
  exact RestrictedProduct.ext _ _ fun w => key w

theorem exists_integer_of_forall (y : D.host.E) (h : ∀ v : Pl D, idem D (· = v) * incA D y ∈ intAt D (· = v)) :
    ∃ b : 𝓞 D.host.E, (b : D.host.E) = y := by
  classical
  obtain ⟨t, ht0, b, hb⟩ := exists_int_mul y
  have hF : (t : D.host.F) ≠ 0 := by exact_mod_cast ht0
  have hfin := Ideal.finite_factors (I := Ideal.span {t}) (by simpa using ht0)
  have h1 : (1 : Af D.host.F) ⊗ₜ[D.host.F] y ∈ intAE D := by
    rw [one_eq_sum hfin.toFinset, TensorProduct.add_tmul, TensorProduct.sum_tmul]
    refine add_mem (sum_mem fun v _ => ?_) ?_
    · have := (h v).2
      rwa [idem_mul_incA, finPart_pair] at this
    · refine AddSubgroup.subset_closure ⟨(t : D.host.F)⁻¹ • ePl D (· ∉ hfin.toFinset), fun w => ?_, b, ?_⟩
      · rw [map_smul, evalV_ePl]
        by_cases hw : w ∈ hfin.toFinset
        · rw [if_neg (not_not.2 hw), smul_zero]; exact zero_mem _
        · rw [if_pos hw, Algebra.smul_def, mul_one]
          refine GlobalTheory.IdVGen.inv_mem_integers fun hm => hw ?_
          rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
          exact hm
      · rw [hb, TensorProduct.smul_tmul, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hF, one_smul]
  have h2 : intAE D ≤ GlobalTheory.AdLat.hat1 D.host.F ((1 : FI D) : Set D.host.E) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, y, rfl⟩
    exact GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral D.host.F ha ((FractionalIdeal.mem_one_iff _).2 ⟨y, rfl⟩)
  exact (FractionalIdeal.mem_one_iff _).1 ((GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff D.host.F 1 y).1 (h2 h1))

theorem idem_ne_zero (v : Pl D) : idem D (· = v) ≠ 0 := by
  intro h
  have := compAt_idem (· = v) v
  rw [h, if_pos rfl, RingHom.map_zero] at this
  exact zero_ne_one this

theorem selfDual_of_local : ∀ (D : D7) (h : D.host.E) (𝔞 : FI D) (u : (AE D)ˣ), (∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ idV 𝔞 x ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) → (∀ x : Pl D, ∀ a ∈ idAt D (· = x), a ∈ intAt D (· = x) ↔ (u : AE D) * cA D (u : AE D) * incA D h * a ∈ intAt D (· = x)) → ∀ d : D.host.E, d ∈ 𝔞 ↔ ∀ c ∈ 𝔞, ∃ b : 𝓞 D.host.E, (b : D.host.E) = star c * d * h := by
  intro D h 𝔞 u H1 H2 d
  have hU : ((u⁻¹ : (AE D)ˣ) : AE D) * (u : AE D) = 1 := u.inv_mul
  have hC : cA D ((u⁻¹ : (AE D)ˣ) : AE D) * cA D (u : AE D) = 1 := by
    rw [← RingHom.map_mul (cA D), hU, RingHom.map_one]
  generalize ((u⁻¹ : (AE D)ˣ) : AE D) = u' at H1 hU hC
  generalize (u : AE D) = u at H2 hU hC
  have hue : ∀ v, u * idem D (· = v) ∈ idV 𝔞 v := fun v =>
    (H1 v _ (Ideal.mul_mem_left _ _ (idem_mem_idAt _))).2 (by rw [← mul_assoc, hU, one_mul]; exact idem_mem_intAt _)
  have loc : ∀ v, ∀ x ∈ 𝔞, u' * (idem D (· = v) * incA D x) ∈ intAt D (· = v) := fun v x hx =>
    (H1 v _ (Ideal.mul_mem_right _ _ (idem_mem_idAt _))).1 (idem_mul_incA_mem hx v)
  constructor
  · intro hd c hc
    refine exists_integer_of_forall _ fun v => ?_
    have h3 := intAt_mul (loc v d hd) (cA_mem_intAt (loc v c hc))
    have h4 := (H2 v _ h3.1).1 h3
    have he := idem_mul_self (D := D) (· = v)
    rw [RingHom.map_mul (cA D), RingHom.map_mul (cA D), cA_idem, GlobalTheory.FinPl.FrameLat.cA_incA] at h4
    rw [RingHom.map_mul (incA D), RingHom.map_mul (incA D), alg₁ hU hC he]
    exact h4
  · intro hd
    have h𝔞 : 𝔞 ≠ 0 := by
      rintro rfl
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      let v : Pl D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField D.host.F)⟩
      have h0 := hue v
      rw [idV_zero, AddSubgroup.mem_bot] at h0
      apply idem_ne_zero v
      rw [← one_mul (idem D (· = v)), ← hU, mul_assoc, h0, mul_zero]
    have s1 : ∀ v, u' * (idem D (· = v) * incA D d) ∈ intAt D (· = v) := by
      intro v
      have hc := mul_cA_mem (y := d * h) (fun c hc => by
        obtain ⟨b, hb⟩ := hd c hc
        exact ⟨b, by rw [hb]; ring⟩) (hue v)
      refine (H2 v _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (idem_mem_idAt _)))).2 ?_
      rw [RingHom.map_mul (cA D), cA_idem, RingHom.map_mul (incA D)] at hc
      rw [alg₂ hU]; exact hc
    rw [← inv_inv 𝔞, FractionalIdeal.mem_inv_iff (inv_ne_zero h𝔞)]
    intro y hy
    refine (FractionalIdeal.mem_one_iff _).2 (exists_integer_of_forall _ fun v => ?_)
    have t := mul_incA_mem (y := y) (fun c hc =>
      (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff h𝔞).1 hy c hc)) (hue v)
    have h5 := intAt_mul (s1 v) t
    have he := idem_mul_self (D := D) (· = v)
    rw [RingHom.map_mul (incA D), alg₃ hU he]
    exact h5

end GlobalTheory.FinPl.SelfDualIdeal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameGlInt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameGlInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mat_int {p : SplitPt D k} {S : HSp D} {L : Lat S} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank)
    (β : Frame p S (Fin S.rank)) {Λ : Submodule 𝒪[k] (Fin S.rank → k)} (h : β.IsLat L Λ) (g : GL (Fin S.rank) k)
    (hg : g • Λ = Λ) (r s : Fin S.rank) : (β.b * g.val * β.b') r s ∈ 𝒪[k] := by
  have hmem : ∀ x, x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := fun x => by
    rw [h x, GlobalTheory.SeeSaw.StdOff.mem_latV_int hL]
    exact forall_congr' fun r =>
      ((p.int_iff _).trans (and_iff_right (GlobalTheory.SeeSaw.StdOff.sec_mem_idAt p _)).symm).symm
  have h1 : β.b' *ᵥ Pi.single s 1 ∈ Λ := (hmem _).2 fun r => by
    rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have h2 : g • (β.b' *ᵥ Pi.single s 1) ∈ Λ := hg ▸ Submodule.smul_mem_pointwise_smul _ _ _ h1
  have h3 := (hmem _).1 h2 r
  convert h3 using 1
  rw [show g • (β.b' *ᵥ Pi.single s 1) = g.val *ᵥ (β.b' *ᵥ Pi.single s 1) from rfl, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

theorem finM_mul (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    GlobalTheory.AdForm.finM V hn (g * h) = GlobalTheory.AdForm.finM V hn g * GlobalTheory.AdForm.finM V hn h := by
  simp [GlobalTheory.AdForm.finM, Formalism.L2.Theta.mt, Matrix.map_mul, Matrix.submatrix_mul_equiv]

theorem prF_finM (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D)
    {n : ℕ} (hn : V.rank = n) (g : GA D V) (r s : Fin n) :
    q.prF he (GlobalTheory.AdForm.finM V hn g r s) = (Formalism.L2.Theta.mt V g).map q.pr ((finCongr hn).symm r) ((finCongr hn).symm s) := by
  simp [GlobalTheory.AdForm.finM, Matrix.reindex_apply, SplitPt.prF_toEAf]

theorem finM_one (V : HSp D) {n : ℕ} (hn : V.rank = n) : GlobalTheory.AdForm.finM V hn 1 = 1 := by
  simp [GlobalTheory.AdForm.finM, Formalism.L2.Theta.mt]

end GlobalTheory.FrameGlInt

namespace GlobalTheory.FrameGlInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option maxHeartbeats 1600000 in
theorem exists_int (p : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt p.e PP) (S : HSp D)
    {n : ℕ} (hn : S.rank = n) (hgram : S.gram.reindex (finCongr hn) (finCongr hn) = 1) {L : Lat S}
    (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank) (β : Frame p S (Fin S.rank)) {Λ : Submodule 𝒪[k] (Fin S.rank → k)}
    (hlat : β.IsLat L Λ) (g : GL (Fin S.rank) k) (hgl : g • Λ = Λ) :
    ∃ δ : GL (Fin n) (GlobalTheory.AdForm.EF D), δ.1 = GlobalTheory.AdForm.finM S hn (β.gl g) ∧
      δ ∈ Formalism.UG.UPts (sigD D) (1 : Matrix (Fin n) (Fin n) D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
      (∀ r r', δ.1 r r' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      (∀ r r', (δ⁻¹).1 r r' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) := by
  obtain ⟨⟨x, hx0⟩, hx⟩ := GlobalTheory.AdForm.RdVal.finM_mem S hn _ hgram.symm (β.gl g)
  refine ⟨x, hx, hx0, ?_⟩
  have hgl' : g⁻¹ • Λ = Λ := by
    conv_lhs => rw [← hgl]
    exact inv_smul_smul g _
  have hcomp : ∀ h : GL (Fin S.rank) k, h • Λ = Λ → ∀ r s,
      toEAf D p.e * GlobalTheory.AdForm.finM S hn (β.gl h) r s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro h hh r s
    rw [← p.prF_mem_iff he]
    have e1 := prF_finM p he S hn (β.gl h) r s
    rw [β.gl_mat h] at e1
    exact e1 ▸ mat_int hL β hlat h hh _ _
  set σ := Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) with hσ

  have hu0 : Formalism.UG.cT σ x.1 * ((1 : Matrix (Fin n) (Fin n) D.host.E).map
      (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) * x.1 =
      (1 : Matrix (Fin n) (Fin n) D.host.E).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := hx0
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at hu0
  have hinvM : (x⁻¹).1 = Formalism.UG.cT σ x.1 := by
    calc (x⁻¹).1 = (Formalism.UG.cT σ x.1 * x.1) * (x⁻¹).1 := by rw [hu0, one_mul]
      _ = _ := by rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

  have hxi : (x⁻¹).1 = GlobalTheory.AdForm.finM S hn (β.gl g⁻¹) := by
    have h1 : x.1 * GlobalTheory.AdForm.finM S hn (β.gl g⁻¹) = 1 := by
      rw [hx, ← finM_mul, ← map_mul, mul_inv_cancel, map_one, finM_one]
    calc (x⁻¹).1 = (x⁻¹).1 * (x.1 * GlobalTheory.AdForm.finM S hn (β.gl g⁻¹)) := by rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  obtain ⟨hf, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D p.e PP he
  have hσmem : ∀ y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, σ y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun y hy => GlobalTheory.Mem.Col2.sigR_mem_rInt D.sp.cm hy
  have hσσ : ∀ y, σ (σ y) = y := Formalism.L2.DIV.sigR_sigR D.sp.cm
  have hcA : toEAf D (cA D p.e) = σ (toEAf D p.e) := GlobalTheory.AdForm.RdVal.toEAf_sig p.e
  have hint : ∀ r r', x.1 r r' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro r r'
    have hs := congrArg (toEAf D) (β.gl_supp g ((finCongr hn).symm r) ((finCongr hn).symm r'))
    have hxr : x.1 r r' = toEAf D (Formalism.L2.Theta.mt S (β.gl g) ((finCongr hn).symm r) ((finCongr hn).symm r')) := by
      rw [hx]; rfl
    have hcm : toEAf D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((finCongr hn).symm r) ((finCongr hn).symm r')) ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [Matrix.one_apply]; split_ifs
      · rw [RingHom.map_one]; exact one_mem _
      · rw [RingHom.map_zero]; exact zero_mem _
    rw [Matrix.sub_apply, RingHom.map_mul, RingHom.map_sub, RingHom.map_add (f := _), hcA, ← hxr] at hs
    have hdec : x.1 r r' = toEAf D p.e * x.1 r r' + σ (toEAf D p.e * (x⁻¹).1 r' r) +
        (1 - toEAf D p.e - σ (toEAf D p.e)) *
          toEAf D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((finCongr hn).symm r) ((finCongr hn).symm r')) := by
      have e2 : σ (toEAf D p.e * (x⁻¹).1 r' r) = σ (toEAf D p.e) * x.1 r r' := by
        rw [hinvM, map_mul]
        show σ (toEAf D p.e) * σ (σ (x.1 r r')) = _
        rw [hσσ]
      rw [e2]
      linear_combination (-1 : GlobalTheory.AdForm.EF D) * hs
    rw [hdec]
    refine add_mem (add_mem ?_ ?_) (mul_mem (sub_mem (sub_mem (one_mem _) hf) (hσmem _ hf)) hcm)
    · exact hx ▸ hcomp g hgl r r'
    · exact hσmem _ (hxi ▸ hcomp g⁻¹ hgl' r' r)
  exact ⟨hint, fun r r' => by
    rw [hinvM]
    exact hσmem _ (hint r' r)⟩

end GlobalTheory.FrameGlInt

theorem GlobalTheory.AdForm.frameGl_int : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 → ∀ (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (s : 𝓀[k]ˣ), g • Q j i = s • Q j i →
    ∃ δ : TC.GA B (B.R.N j), δ.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) ∧ δ ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N j) ∧
      (∀ r r', δ.1 r r' ∈ Formalism.L2.DIV.RInt B.host.F B.host.E) ∧ (∀ r r', (δ⁻¹).1 r r' ∈ Formalism.L2.DIV.RInt B.host.F B.host.E) := by
  intro B X I hOk hPins l Z u a k _ _ _ _ ι p β Q L hStd j hj i v hIdem g s hgs
  have hg1 : gramN (I.rec7 l Z) j hj = 1 := ((TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 j hj).1
  obtain ⟨-, hT⟩ := hStd
  obtain ⟨hL, hT'⟩ := hT j hj
  obtain ⟨hlat, -⟩ := hT' i
  have hgl : g • (Q j i).lat = (Q j i).lat := by
    have := congrArg GlobalTheory.LatPair.Pair.lat hgs
    rwa [GlobalTheory.LatPair.Pair.smul_lat, GlobalTheory.LatPair.Pair.dia_lat] at this
  obtain ⟨δ, h1, h2, h3, h4⟩ := GlobalTheory.FrameGlInt.exists_int (p i) hIdem _ (rankN (I.rec7 l Z) j hj) hg1 hL (β j i) hlat g hgl
  exact ⟨δ, h1, h2, h3, h4⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateVectorsChainSpaceSelfDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem intVec_isSelfDualC : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (j : ℕ), j ≤ B.R.m →
    ∀ L : Lat ((I.rec7 l Z).sp.X j), (∀ z, z ∈ L ↔ z ∈ intVec (I.rec7 l Z) _) → IsSelfDualC ((I.rec7 l Z).sp.X j) L := by
  intro B X I hI l Z j hj L hL
  have hG : ((I.rec7 l Z).sp.X j).gram = 1 := GlobalTheory.AdForm.PinInhab.gram_X hI j
  have hm : ∀ x : Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E,
      x ∈ Examples₂.stdLat _ ↔ ∀ i, IsIntegral ℤ (x i) := fun x => by
    rw [Examples₂.stdLat, Module.Basis.mem_span_iff_repr_mem]
    exact forall_congr' fun i => ⟨fun ⟨b, hb⟩ => by rw [← show _ = x i from hb]; exact b.2,
      fun h => ⟨⟨_, h⟩, rfl⟩⟩
  have hLe : L = Examples₂.stdLat _ := by
    ext z
    rw [hL z, hm]
    rfl
  subst hLe
  refine ⟨Examples₂.stdLat_isLattice _, fun y => GlobalTheory.Ker.Inhab.selfDual_diag (fun _ => false) _ (fun i k => ?_) y⟩
  rw [hG, Matrix.one_apply]
  simp [Examples₂.sgn]

end GlobalTheory.AdForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsKFinOfMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.CommIs

open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt GlobalTheory.Core.Mi

theorem isKFin_of_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {x : M.H τ}
    (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) : Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) x := by
  induction hx using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ v hv => by
      rw [(Submodule.mem_bot _).1 hv, map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h1, h2, h3⟩ := hx
    obtain ⟨S₂, k1, k2, k3⟩ := hy
    refine ⟨S₁ ⊔ S₂, inferInstance, Submodule.add_mem_sup h2 k2, fun g hg v hv => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h3 g hg a ha) (k3 g hg b hb)
  | smul c x _ hx =>
    obtain ⟨S₁, h1, h2, h3⟩ := hx
    exact ⟨S₁, h1, S₁.smul_mem c h2, h3⟩

theorem itSpans_of (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V W : HSp D}
    {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
    (aS aT : D.what₂.Tau → ℚ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ)
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hθ : IsInfFam θ) (hw : IsWeilExp ψ V W aS aT ω)
    (hv : IsVacVec ψ θ M M' f) (hi : IsItW θ M M' ω (ptOf ψ θ M M' f) It) : GlobalTheory.Core.Mi.ItSpans M M' It := by
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D V W S S' M M' θ ψ aS aT ω f It hθ hw hv hi
  intro v hv
  have hv' := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  refine (Submodule.span_le.2 ?_) hv'
  rintro w ⟨P, u, hu, rfl⟩
  have hu' : u ∈ Submodule.comap (It P) (Submodule.span ℂ
      {x | ∃ (P : PolF D W.rank V.rank) (y : M'.Vec), GlobalTheory.Core.Mi.KVecP M' y ∧ x = It P (PiTensorProduct.tprod ℂ y)}) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨P, y, fun τ => isKFin_of_mem _ _ (hy τ), rfl⟩
  exact hu'

end GlobalTheory.Fam.CommIs


open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt in
theorem GlobalTheory.Fam.commOf_is : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ g : GlobalTheory.Fam.Geo D, GeoMeas (pk W) g → (∀ j, j ≤ D.R.m → (g.x j).Is) → (commOf (pk W) u g).Is := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W u hp g hm hx
  have hC : W.Q.Rl.Char3 W.Q.F := hp.bot.hyp.2.2.2.1
  have hS : StepsOK (pk W) := GlobalTheory.Chain.StepVac.stepsOK _ _ _ _ _ _ (pk W) hC.lev hC.models.inf hC.chain.ωY hC.chain.ωX
    hC.chain.vY hC.chain.vX
  have hθ : IsInfFam (pk W).θ := hC.models.inf
  have hm1 : D.R.m - 1 < D.R.m := Nat.sub_lt (lt_of_lt_of_le two_pos D.R.two_le_m) one_pos
  have hY : ∀ j, j + 1 < D.R.m → GlobalTheory.Core.Mi.ItSpans ((pk W).MY j) ((pk W).MY (j + 1)) ((pk W).ItY j) := by
    intro j hj
    have h := hS.1 W.P.A3.A.μ0 ⟨j, by omega⟩ hj
    obtain ⟨χS, χT, hω, he⟩ := h.1
    exact GlobalTheory.Fam.CommIs.itSpans_of hDS hHC _ _ _ _ _ _ _ _ _ hθ ⟨χS, χT, hω, he⟩ h.2 (hC.chain.ItY W.P.A3.A.μ0 j hj)
  have hX : GlobalTheory.Core.Mi.ItSpans ((pk W).MY (D.R.m - 1)) (pk W).MX (pk W).ItX := by
    have h := hS.2 W.P.A3.A.μ0 ⟨D.R.m - 1, hm1⟩ rfl
    obtain ⟨χS, χT, hω, he⟩ := h.1
    exact GlobalTheory.Fam.CommIs.itSpans_of hDS hHC _ _ _ _ _ _ _ _ _ hθ ⟨χS, χT, hω, he⟩ h.2 (hC.chain.ItX W.P.A3.A.μ0)
  have hXc : ∀ n (e : D.R.m - 1 = n), GlobalTheory.Core.Mi.ItSpans ((pk W).MY n) (pk W).MX
      (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT (pk W).MX →ₗ[ℂ] SmT ((pk W).MY n))
        (pk W).ItX e) := by
    intro n e
    subst e
    exact hX
  refine ⟨W.Q.stdChar, hθ, hx, GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite D.sp.X'_sig fun τ => Or.inl (D.X'_posDef τ), hm.μf, hm.ρJ,
    hm.ρB, fun j hj => hY j hj, fun j h => hXc (j + 1) (idx_top h)⟩
end
end

