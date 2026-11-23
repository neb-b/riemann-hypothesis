module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSplitPlacesActsBySigns
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.VacSign

theorem af_ext' {D : D7} {x y : Af D.host.F} (h : ∀ w, evalV D.host.F w x = evalV D.host.F w y) : x = y :=
  Subtype.ext (funext fun w => h w)

theorem latO_acts_by_signs : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P, ∃ ε : ℂ, ε * ε = 1 ∧ ∀ f, Vac ψ S T LS LT P f → heisO ψ S T x f = ε • f := by
  intro D k _ _ _ _ ι p I P hP ψ hψ S T LS LT hS hT x hx
  classical
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
    exact ⟨α, hα, fun v hv => hs v fun h => hv ((hP.mem v).2 ⟨i, h⟩), rest⟩
  have piece : ∀ i, ∀ w ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v),
      w ∈ G := by
    intro i w hw
    obtain ⟨h1, h2⟩ := GlobalTheory.SplitVac.idem_latO D k (p i) S T LS LT w hw
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
      have hdec : α = ∑ i ∈ I.toFinset, GlobalTheory.FinPl.LatMem.indP D.host.F (· = (p i).v) * α := by
        apply af_ext'
        intro v
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [map_mul, GlobalTheory.FinPl.LatMem.evalV_indP]
        by_cases hv : P v
        · obtain ⟨i, rfl⟩ := (hP.mem v).1 hv
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hj
            rw [if_neg (fun h => hj (hP.inj h).symm), zero_mul]
          · intro h
            exact absurd (List.mem_toFinset.2 (hP.all i)) h
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

end GlobalTheory.FinPl.VacSign

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.KSplit

open GlobalTheory.FinPl.SetCut

variable {D : D7}

theorem idAt_mono {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D P' := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
  exact ⟨ha.1, fun w hw => ha.2 w fun h' => hw (h w h')⟩

theorem latV_mono (V : HSp D) (L : Lat V) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) : latV V L P ≤ latV V L P' := by
  apply AddSubgroup.closure_mono
  rintro y ⟨α, hα, h0, r⟩
  exact ⟨α, hα, fun v hv => h0 v fun h' => hv (h v h'), r⟩

theorem mul_mem_idAt {P R : Pl D → Prop} {c : AE D} (hc : ∀ w, ¬ R w → compAt D w c = 0) {a : AE D}
    (ha : a ∈ idAt D P) : c * a ∈ idAt D (fun p => P p ∧ R p) := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
  refine ⟨by rw [RingHom.map_mul, ha.1, mul_zero], fun w hw => ?_⟩
  rw [RingHom.map_mul]
  by_cases h : R w
  · rw [ha.2 w fun h' => hw ⟨h', h⟩, mul_zero]
  · rw [hc w h, zero_mul]

theorem smul_mem_latV (V : HSp D) (L : Lat V) {P R : Pl D → Prop} (β : Af D.host.F) (hβ : β ∈ intAf D.host.F)
    (h0 : ∀ v, ¬ R v → evalV D.host.F v β = 0) {y : Fin V.rank → AE D} (hy : y ∈ latV V L P) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) • y ∈ latV V L (fun p => P p ∧ R p) := by
  have main : latV V L P ≤ (latV V L (fun p => P p ∧ R p)).comap
      (DistribSMul.toAddMonoidHom (Fin V.rank → AE D) (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β))) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hα0, a, ha, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨β * α, fun v => by rw [map_mul]; exact mul_mem (hβ v) (hα v), fun v hv => ?_,
      a, ha, x, hx, ?_⟩
    · rw [map_mul]
      by_cases h : R v
      · rw [hα0 v fun h' => hv ⟨h', h⟩, mul_zero]
      · rw [h0 v h, zero_mul]
    · funext i
      change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  exact main hy

theorem indQ_int (Q : Finset (Pl D)) : indQ D Q ∈ intAf D.host.F := by
  intro v
  rw [evalV_indQ]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem indQc_int (Q : Finset (Pl D)) : 1 - indQ D Q ∈ intAf D.host.F := by
  intro v
  rw [map_sub, map_one]
  exact sub_mem (one_mem _) (indQ_int Q v)

abbrev eQ (Q : Finset (Pl D)) : AE D := algebraMap (AF D.host.F) (AE D) (idemQ D Q)

theorem eQ_off (Q : Finset (Pl D)) (w : Pl D) (hw : ¬ w ∈ Q) : compAt D w (eQ Q) = 0 := by
  rw [(parts_idemQ Q).2 w, if_neg hw]

theorem one_sub_eQ_off (Q : Finset (Pl D)) (w : Pl D) (hw : ¬ w ∉ Q) : compAt D w (1 - eQ Q) = 0 := by
  rw [RingHom.map_sub, RingHom.map_one, (parts_idemQ Q).2 w, if_pos (not_not.1 hw), sub_self]

theorem eQ_mul_of_in {P : Pl D → Prop} (Q : Finset (Pl D)) {a : AE D} (ha : a ∈ idAt D (fun p => P p ∧ p ∈ Q)) :
    eQ Q * a = a :=
  (mem_idAt_Q_iff Q a).1 (idAt_mono (fun _ h => h.2) ha)

theorem eQ_mul_of_out {P : Pl D → Prop} (Q : Finset (Pl D)) {a : AE D} (ha : a ∈ idAt D (fun p => P p ∧ p ∉ Q)) :
    eQ Q * a = 0 := by
  classical
  refine (mem_idOff_iff_mul (· ∈ Q) _ (parts_idemQ Q).1 (fun w => by convert (parts_idemQ Q).2 w) a).1 ?_
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]
  intro w hw
  exact ((mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere _ _ _).1 ha).2 w fun h => h.2 hw

theorem one_sub_mul_eq {P : Pl D → Prop} (Q : Finset (Pl D)) {a : AE D} (ha : a ∈ idAt D P) :
    (1 - eQ Q) * a = algebraMap (AF D.host.F) (AE D) (idemQc D Q) * a := by
  rw [← sub_eq_zero]
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha
  apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, ha.1, mul_zero, mul_zero, sub_zero]
  · intro w
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, (parts_idemQ Q).2 w,
      (parts_idemQc Q).2 w]
    split_ifs
    · rw [sub_self, sub_self]
    · rw [sub_zero, sub_self]

theorem mem_latV_iff_parts (V : HSp D) (L : Lat V) (P : Pl D → Prop) (Q : Finset (Pl D)) {y : Fin V.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV V L P ↔ eQ Q • y ∈ latV V L (fun p => P p ∧ p ∈ Q) ∧
      (1 - eQ Q) • y ∈ latV V L (fun p => P p ∧ p ∉ Q) := by
  constructor
  · intro h
    refine ⟨smul_mem_latV V L (indQ D Q) (indQ_int Q) (fun v hv => by rw [evalV_indQ, if_neg hv]) h, ?_⟩
    have e : (1 - eQ Q) • y = algebraMap (AF D.host.F) (AE D) (idemQc D Q) • y :=
      funext fun i => one_sub_mul_eq Q (hy i)
    rw [e]
    exact smul_mem_latV V L (1 - indQ D Q) (indQc_int Q)
      (fun v hv => by rw [map_sub, map_one, evalV_indQ, if_pos (not_not.1 hv), sub_self]) h
  · rintro ⟨h1, h2⟩
    have e : y = eQ Q • y + (1 - eQ Q) • y := by rw [← add_smul, add_sub_cancel, one_smul]
    rw [e]
    exact add_mem (latV_mono V L (fun _ h => h.1) h1) (latV_mono V L (fun _ h => h.1) h2)

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := rfl

theorem mt_inj (V : HSp D) {a b : GA D V} (h : mt V a = mt V b) : a = b :=
  Subtype.ext (Units.ext h)

theorem mulVec_mem (V : HSp D) {I : Ideal (AE D)} (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    {y : Fin V.rank → AE D} (hy : ∀ i, y i ∈ I) (i : Fin V.rank) : (M *ᵥ y) i ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact I.sum_mem fun j _ => I.mul_mem_left _ (hy j)

section Ring

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem cut_sub_one (c : A) (M : Matrix n n A) : c • M + (1 - c) • (1 : Matrix n n A) - 1 = c • (M - 1) := by
  module

theorem cut_mulVec (c : A) (M : Matrix n n A) (y : n → A) (hy : c • y = y) :
    (c • M + (1 - c) • (1 : Matrix n n A)) *ᵥ y = M *ᵥ y := by
  rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, ← mulVec_smul, hy, sub_smul, hy, one_smul, sub_self, add_zero]

theorem cut_mul_cut (c : A) (hc : c * c = c) (M : Matrix n n A) :
    (c • M + (1 - c) • (1 : Matrix n n A)) * ((1 - c) • M + (1 - (1 - c)) • (1 : Matrix n n A)) = M := by
  have h1 : c * (1 - c) = 0 := by linear_combination -hc
  have h2 : (1 - c) * c = 0 := by linear_combination -hc
  have h3 : (1 - c) * (1 - c) = 1 - c := by linear_combination hc
  simp only [sub_sub_cancel, add_mul, mul_add, smul_mul_smul_comm, h1, h2, h3, hc, zero_smul, mul_one, one_mul,
    zero_add, add_zero]
  module

theorem prod_parts (c : A) (a b : Matrix n n A) (ha : c • (a - 1) = a - 1) (hb : c • (b - 1) = 0) (y : n → A) :
    c • ((a * b) *ᵥ y) = a *ᵥ (c • y) ∧ (1 - c) • ((a * b) *ᵥ y) = b *ᵥ ((1 - c) • y) := by
  have h1 : c • b = c • (1 : Matrix n n A) := by rw [← sub_eq_zero, ← smul_sub, hb]
  have h2 : (1 - c) • a = (1 - c) • (1 : Matrix n n A) := by
    rw [← sub_eq_zero, ← smul_sub, sub_smul, ha, one_smul, sub_self]
  constructor
  · rw [← smul_mulVec, ← mul_smul_comm, h1, mul_smul_comm, mul_one, smul_mulVec, mulVec_smul]
  · rw [← smul_mulVec, ← smul_mul_assoc, h2, smul_mul_assoc, one_mul, smul_mulVec, mulVec_smul]

end Ring

theorem inK_cut (V : HSp D) (L : Lat V) {P R : Pl D → Prop} (ε : AF D.host.F) (hε : ε * ε = ε)
    (hoff : ∀ w, ¬ R w → compAt D w (algebraMap (AF D.host.F) (AE D) ε) = 0)
    (hone : ∀ a ∈ idAt D (fun p => P p ∧ R p), algebraMap (AF D.host.F) (AE D) ε * a = a)
    (hlat : ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D P) → y ∈ latV V L P →
      algebraMap (AF D.host.F) (AE D) ε • y ∈ latV V L (fun p => P p ∧ R p))
    {κ : GA D V} (hκ : InK V L P κ) : InK V L (fun p => P p ∧ R p) (cutG V ε hε κ) := by
  have key : ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (fun p => P p ∧ R p)) →
      (y ∈ latV V L (fun p => P p ∧ R p) ↔ y ∈ latV V L P) := by
    intro y hy
    refine ⟨fun h => latV_mono V L (fun _ h => h.1) h, fun h => ?_⟩
    have e : algebraMap (AF D.host.F) (AE D) ε • y = y := funext fun i => hone _ (hy i)
    have := hlat y (fun i => idAt_mono (fun _ h => h.1) (hy i)) h
    rwa [e] at this
  refine ⟨(mem_congGrp_iff V _ _).2 fun i j => ?_, fun y hy => ?_⟩
  · rw [mt_cutG, cut_sub_one]
    exact mul_mem_idAt hoff ((mem_congGrp_iff V _ _).1 hκ.1 i j)
  · have e : algebraMap (AF D.host.F) (AE D) ε • y = y := funext fun i => hone _ (hy i)
    rw [mt_cutG, cut_mulVec _ _ _ e, key y hy, key _ (mulVec_mem V _ hy)]
    exact hκ.2 y fun i => idAt_mono (fun _ h => h.1) (hy i)

theorem inK_iff_prod : ∀ (D : D7) (V : HSp D) (L : Lat V) (P : Pl D → Prop) (Q : Finset (Pl D)) (κ : GA D V),
    InK V L P κ ↔ ∃ a b, InK V L (fun p => P p ∧ p ∈ Q) a ∧ InK V L (fun p => P p ∧ p ∉ Q) b ∧ κ = a * b := by
  intro D V L P Q κ
  have e1 : algebraMap (AF D.host.F) (AE D) (1 - idemQ D Q) = 1 - eQ Q := by rw [map_sub, map_one]
  constructor
  · intro hκ
    refine ⟨cutG V _ (idemQ_mul_self Q) κ, cutG V _ (one_sub_idemQ_mul_self Q) κ,
      inK_cut V L _ _ (eQ_off Q) (fun a ha => eQ_mul_of_in Q ha)
        (fun y hy h => ((mem_latV_iff_parts V L P Q hy).1 h).1) hκ,
      inK_cut V L _ _ (by rw [e1]; exact one_sub_eQ_off Q)
        (fun a ha => by rw [e1, sub_mul, eQ_mul_of_out Q ha, one_mul, sub_zero])
        (fun y hy h => by rw [e1]; exact ((mem_latV_iff_parts V L P Q hy).1 h).2) hκ, mt_inj V ?_⟩
    rw [mt_mul, mt_cutG, mt_cutG, e1]
    exact (cut_mul_cut _ (by rw [← map_mul, idemQ_mul_self]) _).symm
  · rintro ⟨a, b, ha, hb, rfl⟩
    have hA := (mem_congGrp_iff V _ _).1 ha.1
    have hB := (mem_congGrp_iff V _ _).1 hb.1
    refine ⟨mul_mem ((mem_congGrp_iff V _ _).2 fun i j => idAt_mono (fun _ h => h.1) (hA i j))
      ((mem_congGrp_iff V _ _).2 fun i j => idAt_mono (fun _ h => h.1) (hB i j)), fun y hy => ?_⟩
    have hp := prod_parts (eQ Q) (mt V a) (mt V b) (Matrix.ext fun i j => eQ_mul_of_in Q (hA i j))
      (Matrix.ext fun i j => eQ_mul_of_out Q (hB i j)) y
    rw [mem_latV_iff_parts V L P Q hy, mem_latV_iff_parts V L P Q (mulVec_mem V _ hy), mt_mul, hp.1, hp.2]
    exact and_congr (ha.2 _ fun i => mul_mem_idAt (eQ_off Q) (hy i))
      (hb.2 _ fun i => mul_mem_idAt (one_sub_eQ_off Q) (hy i))

end GlobalTheory.FinPl.KSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIffUpMemStdHom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdHomAt
open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem latO_mono (S T : HSp D) (LS LT) {P Q : Pl D → Prop} (h : ∀ v, P v → Q v) :
    latO S T LS LT P ≤ latO S T LS LT Q :=
  AddSubgroup.closure_mono fun _ ⟨α, h1, h2, h3⟩ => ⟨α, h1, fun v hv => h2 v fun hp => hv (h v hp), h3⟩

theorem mem_latO_at (q : SplitPt D k) {S T : HSp D} {LS LT} {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True)
    (hh : IsHalf q.e u) : u ∈ latO S T LS LT (· = q.v) := by
  obtain ⟨ε, ⟨β, rfl, h1, h0⟩, hsum⟩ := q.above
  have hβ : β ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have main : (latO S T LS LT fun _ => True) ≤ (latO S T LS LT (· = q.v)).comap
      (DistribSMul.toAddMonoidHom (WO S T) (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β))) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨β * α, fun v => by rw [map_mul]; exact mul_mem (hβ v) (hα v), fun v hv => ?_,
      a, ha, s, hs, t, ht, ?_⟩
    · rw [map_mul, h0 v hv, zero_mul]
    · ext i j
      change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Matrix.of_apply]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  have h := main hu
  rw [AddSubgroup.mem_comap] at h
  convert h using 1
  ext i j
  change _ = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) * u i j
  rw [← hsum, ← hh i j, ← mul_assoc, add_mul, q.split.1, mul_comm (cA D q.e), q.split.2.1, add_zero]

theorem int_iff_up_mem_stdHom : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ z, z ∈ LS ↔ z ∈ intVec D S.rank) → (∀ z, z ∈ LT ↔ z ∈ intVec D T.rank) → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) ↔ (GlobalTheory.LocMod.ofSplit q).up FS FT x ∈ stdHom S T := by
  intro D k _ _ _ _ q hq Y Y' _ _ _ _ S T FS FT LS LT hS hT eS eT hFS hFT x
  have eS' : (LS : Set (Fin S.rank → D.host.E)) = intVec D S.rank := Set.ext eS
  have eT' : (LT : Set (Fin T.rank → D.host.E)) = intVec D T.rank := Set.ext eT
  rw [stdHom, ← eS', ← eT']
  refine ⟨fun hx => latO_mono S T _ _ (fun _ _ => trivial)
    (GlobalTheory.UpMem.up_mem_latO D k q hq Y Y' S T FS FT LS LT hS hT hFS hFT x hx), fun hx => ?_⟩
  have hh := Witness.up_half (ofSplit q) FS FT x
  obtain ⟨x', hx', e⟩ := GlobalTheory.HalfIntUp.exists_int_up D k q hq Y Y' S T FS FT LS LT hS hT hFS hFT _ (mem_latO_at q hx hh) hh
  have := congrArg ((ofSplit q).down FS FT) e
  rw [Witness.down_up, Witness.down_up] at this
  rwa [this]

end GlobalTheory.StdHomAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocalModelTensorWithHalfFunction
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.TensorModel

variable {D : D7}

theorem cA_invol (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [show cA D (cA D (a ⊗ₜ[D.host.F] x)) = a ⊗ₜ[D.host.F] star (star x) from rfl, star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem symplO_add_left' (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  unfold symplO hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem half_sum {m n : ℕ} {e e' : AE D} (he : e * e' = 0) {u : Mx D m n} (hu : IsHalf e' u) : IsHalf (e + e') u :=
  fun i j => by
    have h0 : e * u i j = 0 := by
      calc e * u i j = e * (e' * u i j) := by rw [hu i j]
        _ = 0 := by rw [← mul_assoc, he, zero_mul]
    rw [add_mul, h0, zero_add, hu i j]

theorem half_sum_cA {m n : ℕ} {e e' : AE D} (he : e * e' = 0) {u : Mx D m n} (hu : IsHalf (cA D e') u) :
    IsHalf (cA D (e + e')) u := by
  rw [map_add (f := _)]
  refine half_sum ?_ hu
  rw [← map_mul, he, map_zero]

theorem symplO_half_zero {S T : HSp D} {e e' : AE D} (he : e * e' = 0) {s y : WO S T} (hs : IsHalf e s)
    (hy : IsHalf (cA D e') y) : symplO S T s y = 0 := by
  have h0 : hO S T s y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h1 : cA D (y c b) = e' * cA D (y c b) := by
      conv_lhs => rw [← hy c b]
      rw [map_mul, cA_invol]
    have h2 : s d a = e * s d a := (hs d a).symm
    rw [h1, h2]
    linear_combination (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * s d a) * he
  unfold symplO
  rw [h0, mul_zero, map_zero]

theorem isModel_tensor : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (e : AE D), e * p.e = 0 → ∀ Φ : WO S T → ℂ, (∀ t, Φ t ≠ 0 → IsHalf e t) → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + p.e) (stdHom S T) 1 f₀ T' → (∀ Φ', IsSBHalf (e + p.e) (stdHom S T) Φ' → IsThetaFunO ψ S T (T' Φ')) → (∀ Ψ ∈ SB (Matrix Y Y' k), IsSBHalf (e + p.e) (stdHom S T) (p.tensorAt FS FT Φ Ψ)) → p.IsModel ψ FS FT (T' ∘ₗ p.tensorL FS FT Φ) := by
  intro D k _ _ _ _ p ψ S T Y Y' _ _ _ _ FS FT e he Φ hΦ f₀ T' hP hθ hSB
  have hup : ∀ x, IsHalf (e + p.e) (p.up FS FT x) := fun x => half_sum he (Witness.up_half p FS FT x)
  refine ⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩
  · exact hθ _ (hSB Ψ.1 Ψ.2)
  · have key : p.tensorAt FS FT Φ Ψ'.1 = fun t => p.tensorAt FS FT Φ Ψ.1 (t + p.up FS FT x) := by
      funext t
      simp only [Place.tensorAt]
      rw [Witness.down_add, Witness.down_up, Witness.up_add, h, add_sub_add_right_eq_sub]
    simp only [LinearMap.comp_apply, Place.tensorL_apply]
    rw [key]
    exact hP.trans _ (hSB Ψ.1 Ψ.2) _ (hup x)
  · have key : p.tensorAt FS FT Φ Ψ'.1 = fun t => ψ (symplO S T t y) * p.tensorAt FS FT Φ Ψ.1 t := by
      funext t
      simp only [Place.tensorAt]
      rw [h]
      by_cases h0 : Φ (t - p.up FS FT (p.down FS FT t)) = 0
      · rw [h0]; ring
      · have e1 : symplO S T t y = symplO S T (t - p.up FS FT (p.down FS FT t)) y +
            symplO S T (p.up FS FT (p.down FS FT t)) y := by
          rw [← symplO_add_left', sub_add_cancel]
        rw [e1, symplO_half_zero he (hΦ _ h0) hy, zero_add]
        ring
    simp only [LinearMap.comp_apply, Place.tensorL_apply]
    rw [key]
    exact hP.modul _ (hSB Ψ.1 Ψ.2) _ (half_sum_cA he hy)

end GlobalTheory.LocMod.TensorModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumIsTwoVariableThetaFunctionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeeSaw_datum_isTwoVariableThetaFunction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), IsThetaFunO ψ V₀ S Ξ → IsThetaFunO ψ S T Φ₂ → IsBiTheta ψ A S X (lastBi o o'' τ Ξ Φ₂) := by
  first | exact @GlobalTheory.LastBiTheta.isBiTheta_lastBi | exact GlobalTheory.LastBiTheta.isBiTheta_lastBi | (intros; apply GlobalTheory.LastBiTheta.isBiTheta_lastBi <;> assumption)
end

