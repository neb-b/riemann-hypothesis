module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0485
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0462
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedInnerIntegralAtFirstOfSplitPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QValInner

variable {D : D7}

theorem pcomb_eq_sum {G : Type} (e : G →₀ ℂ) (F : G → ℂ) : GlobalTheory.PosOne.comb e F = ∑ a ∈ e.support, e a * F a := rfl

theorem pcomb_congr {G : Type} (e : G →₀ ℂ) {F F' : G → ℂ} (h : ∀ a ∈ e.support, F a = F' a) :
    GlobalTheory.PosOne.comb e F = GlobalTheory.PosOne.comb e F' :=
  Finset.sum_congr rfl fun a ha => by show e a * F a = e a * F' a; rw [h a ha]

theorem pcomb_mapDomain {G H : Type} (e : G →₀ ℂ) (φ : G → H) (F : H → ℂ) :
    GlobalTheory.PosOne.comb (e.mapDomain φ) F = GlobalTheory.PosOne.comb e (fun a => F (φ a)) := by
  classical
  unfold GlobalTheory.PosOne.comb
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem pcomb_fsum {G ι : Type} (f : ι →₀ ℂ) (k : ι → ℂ → (G →₀ ℂ)) (F : G → ℂ) :
    GlobalTheory.PosOne.comb (f.sum k) F = f.sum fun a b => GlobalTheory.PosOne.comb (k a b) F :=
  Finsupp.sum_sum_index (h := fun g a => a * F g) (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem pcomb_single {G : Type} (x : G) (y : ℂ) (F : G → ℂ) : GlobalTheory.PosOne.comb (Finsupp.single x y) F = y * F x :=
  Finsupp.sum_single_index (h := fun g a => a * F g) (zero_mul _)

theorem pcomb_conv_cons {G : Type} [Monoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) (F : G → ℂ) :
    GlobalTheory.PosOne.comb (conv (e :: l)) F =
      GlobalTheory.PosOne.comb (conv l) (fun b => GlobalTheory.PosOne.comb e (fun a => F (a * b))) := by
  classical
  show GlobalTheory.PosOne.comb ((e.sum fun g a => (conv l).sum fun h b => Finsupp.single (g * h) (a * b))) F = _
  rw [pcomb_fsum]
  have e1 : ∀ g a, GlobalTheory.PosOne.comb ((conv l).sum fun h b => Finsupp.single (g * h) (a * b)) F =
      (conv l).sum fun h b => a * b * F (g * h) := fun g a => by
    rw [pcomb_fsum]; exact Finsupp.sum_congr fun h _ => pcomb_single _ _ _
  simp only [e1]
  show (e.sum fun g a => (conv l).sum fun h b => a * b * F (g * h)) = (conv l).sum fun b c => c * (e.sum fun a d => d * F (a * b))
  rw [Finsupp.sum_comm]
  refine Finsupp.sum_congr fun b _ => ?_
  simp only [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun a _ => ?_
  ring

theorem conv_support_mem {G : Type} [Monoid G] (M : Submonoid G) (l : List (G →₀ ℂ))
    (h : ∀ e ∈ l, ∀ g ∈ e.support, g ∈ M) : ∀ g ∈ (conv l).support, g ∈ M := by
  classical
  induction l with
  | nil =>
    intro g hg
    have : g = 1 := by simpa [conv] using Finsupp.support_single_subset hg
    exact this ▸ M.one_mem
  | cons e l ih =>
    intro g hg
    have ih' := ih fun e' he' => h e' (List.mem_cons_of_mem _ he')
    change g ∈ (e.sum fun g a => (conv l).sum fun h b => Finsupp.single (g * h) (a * b)).support at hg
    obtain ⟨x, hx, hg⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hg)
    obtain ⟨y, hy, hg⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hg)
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]
    exact M.mul_mem (h e List.mem_cons_self x hx) (ih' y hy)

theorem comb_eq_fsum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c f = c.sum fun u a => a • heisO ψ S T u f := rfl

theorem comb_aconv_cons (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (l : List (WO S T →₀ ℂ))
    (h : ∀ x ∈ c.support, ∀ y ∈ (aconv l).support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (aconv (c :: l)) f = comb ψ S T c (comb ψ S T (aconv l) f) := by
  classical
  rw [GlobalTheory.HeisComb.comb_comb]
  show comb ψ S T ((c.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b))) f = _
  rw [comb_eq_fsum, Finsupp.sum_sum_index (h := fun u a => a • heisO ψ S T u f) (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  refine Finset.sum_congr rfl fun x hx => ?_
  beta_reduce
  rw [Finsupp.sum_sum_index (h := fun u a => a • heisO ψ S T u f) (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  refine Finset.sum_congr rfl fun y hy => ?_
  beta_reduce
  rw [Finsupp.sum_single_index (h := fun u a => a • heisO ψ S T u f) (zero_smul ℂ _), GlobalTheory.WeilVacMove.heisO_heisO]
  have h0 : symplOH S T x y = 0 := by unfold symplOH; rw [h x hx y hy, mul_zero]
  rw [h0, AddChar.map_zero_eq_one, one_smul]

end GlobalTheory.QValInner

namespace GlobalTheory.QValInner
open GlobalTheory.Grow
variable {D : D7}

theorem congGrp_le (V : HSp D) {I J : Ideal (AE D)} (hIJ : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro x hx
  rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply] at hx ⊢
  have e : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) (matHom V x) =
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.factor hIJ)
        (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) (matHom V x)) := by
    ext i j
    simp
  rw [e, hx, map_one]

theorem grpOff_le_at' (V : HSp D) {P : Pl D → Prop} {v : Pl D} (hv : P v) : grpOff V P ≤ grpOff V (· = v) := by
  apply congGrp_le
  exact le_iInf fun w => iInf_le_of_le ⟨w.1, by rw [w.2]; exact hv⟩ le_rfl

theorem grpAt_le_grpOff' (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → ¬ P' p) : grpAt V P ≤ grpOff V P' := by
  apply congGrp_le
  intro a ha
  refine (Submodule.mem_iInf _).2 fun w => ?_
  exact (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 ha).2 ⟨w.1, fun hp => h w.1 hp w.2⟩

theorem quotient_integral_fsum {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G} {ρ : Measure R} {μ : Measure G}
    {ι : Type} (s : Finset ι) (g : ι → G → ℂ) (z : ι → ℂ) (hs : ∀ i ∈ s, IsQuotIntL1 ρ μ (g i) (z i)) :
    IsQuotIntL1 ρ μ (fun h => ∑ i ∈ s, g i h) (∑ i ∈ s, z i) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun h => ∑ i ∈ (∅ : Finset ι), g i h) = 0 := by funext h; simp
    rw [e, Finset.sum_empty]
    exact IsQuotIntL1.zero
  · intro a s ha ih hs
    have := (hs a (Finset.mem_insert_self a s)).add (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha]
    convert this using 1
    funext h
    simp [Finset.sum_insert ha]

end GlobalTheory.QValInner

namespace GlobalTheory.QValInner

theorem rest_grp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S),
    Function.Injective (fun i => (Q i).q.v) →
    ∀ a ∈ (conv (List.ofFn fun i : Fin r => (Q i.succ).e₀.mapDomain (Q i.succ).gl₀)).support, a ∈ grpOff S.B.V (· = (Q 0).q.v) := by
  classical
  intro D ψ σ S r Q hinj
  refine conv_support_mem (grpOff S.B.V (· = (Q 0).q.v)).toSubmonoid _ ?_
  intro e he g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
  have hr := (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (Q i.succ).k (Q i.succ).q S.B.V _ (Q i.succ).F.G₀ (Q i.succ).gl₀ (Q i.succ).loc₀).2.1
  have ha : (Q i.succ).gl₀ a ∈ grpAt S.B.V (· = (Q i.succ).q.v) := hr ▸ ⟨a, rfl⟩
  refine grpAt_le_grpOff' _ ?_ ha
  rintro p rfl h
  exact Fin.succ_ne_zero i (hinj h)

end GlobalTheory.QValInner

namespace GlobalTheory.QValInner

theorem innerVal_iter2 : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ m₁ s₁ m₂ s₂, LocNorm (Q 0) m₁ s₁ m₂ s₂ → ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ → ∀ x ∈ grpAt S.J.W (places fun i => Q i.succ), ∀ y ∈ grpAt S.B'.V (places fun i => Q i.succ), Iter2 s₁ m₁ s₂ m₂ (fun x₀ y₀ => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x * (Q 0).gl₁ x₀) (y * (Q 0).gl₂ y₀)) (innerVal Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y) := by
  classical
  intro D ψ hψ σ S r Q hinj m₁ s₁ m₂ s₂ hL c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH x hx y hy
  obtain ⟨hc, t1, t2, hv, hφ, hf, ht, hg, hh₁, hh₂⟩ := hH
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hL
  have hc2 : (Q 0).c = 2 * σ := by have := (Q 0).F.bes'.1; omega
  obtain ⟨⟨fc₁, aw₁, or₁⟩, ⟨fc₂, aw₂, or₂⟩⟩ := _root_.GlobalTheory.QVal.inner_supp D ψ σ S r Q hinj
  have hdisj : ∀ p, (places fun i : Fin r => Q i.succ) p → ¬ (p = (Q 0).q.v) := by
    rintro p ⟨i, rfl⟩ h
    exact Fin.succ_ne_zero i (hinj h)
  have hP0 : (places Q) ((Q 0).q.v) := ⟨0, rfl⟩
  have hx0 : x ∈ grpOff S.J.W (· = (Q 0).q.v) := grpAt_le_grpOff' _ hdisj hx
  have hy0 : y ∈ grpOff S.B'.V (· = (Q 0).q.v) := grpAt_le_grpOff' _ hdisj hy
  have hg0 : g ∈ grpOff S.B.V (· = (Q 0).q.v) := grpOff_le_at' _ hP0 hg
  have hh₁0 : h₁ ∈ grpOff S.J.W (· = (Q 0).q.v) := grpOff_le_at' _ hP0 hh₁
  have hh₂0 : h₂ ∈ grpOff S.B'.V (· = (Q 0).q.v) := grpOff_le_at' _ hP0 hh₂
  have hE := rest_grp D ψ σ S r Q hinj
  have hcomm := (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (Q 0).k (Q 0).q S.B.V _ (Q 0).F.G₀ (Q 0).gl₀ (Q 0).loc₀).2.2.2.1
  set E := conv (List.ofFn fun i : Fin r => (Q i.succ).e₀.mapDomain (Q i.succ).gl₀) with hEdef
  set f₁' := comb ψ _ _ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)) f₁ with hf₁'
  set f₂' := comb ψ _ _ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)) f₂ with hf₂'
  have hvac : (Q 0).Vac f₁' f₂' := _root_.GlobalTheory.VacAway.vac_comb D ψ hψ σ S (Q 0) _ _ fc₁ fc₂ aw₁ aw₂ f₁ f₂ t1 t2 (hv 0)

  let Gf : GA D S.B.V → GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k → GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k → ℂ :=
    fun a' x₀ y₀ => GlobalTheory.PosOne.comb (Q 0).e₀ fun a => S.val c₁ c₂ (comb ψ _ _ (Q 0).D₁ f₁') (comb ψ _ _ (Q 0).D₂ f₂') φ f
      (g * a' * (Q 0).gl₀ a) (h₁ * x * (Q 0).gl₁ x₀) (h₂ * y * (Q 0).gl₂ y₀)
  let Z : GA D S.B.V → ℂ := fun a' => (Q 0).volJ * ∑ γ : (Q 0).A₁, ∑ β : (Q 0).A₂, (Q 0).w₁ γ * (Q 0).w₂ β *
    S.val (aconv [c₁, (Q 0).d₁ γ]) (aconv [c₂, (Q 0).d₂ γ β]) f₁' f₂' φ (trc (((Q 0).e₂ β).mapDomain (Q 0).gl₂) f)
      (g * a') (h₁ * x) (h₂ * y)
  have cv := _root_.GlobalTheory.HaarR.quot_int_haar (Q 0).k (Q 0).ν (Q 0).unitVol
  have cv2 := ((cv (Q 0).n₂ ((Q 0).c + 1) (σ + 1) (Q 0).m₂ m₂ (Q 0).haar₂ a5 (Q 0).vol₂).1 (by omega) s₂ a7 a8).2
  have cv1 := ((cv (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1) (Q 0).m₁ m₁ (Q 0).haar₁ a1 (Q 0).vol₁).2 (by omega) (by omega) s₁ a3 a4).2
  have hV : ∀ a', ∃ u : GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k → ℂ, a' ∈ E.support →
      (∀ x₀, IsQuotIntL1 s₂ m₂ (Gf a' x₀) (u x₀)) ∧ IsQuotIntL1 s₁ m₁ u (Z a') := by
    intro a'
    by_cases ha : a' ∈ E.support
    · obtain ⟨u, hu1, hu2⟩ := _root_.GlobalTheory.ValOneAt.valOne_all D ψ hψ σ S (Q 0) m₁ m₂ a1 a5 a2 a6 c₁ c₂ (hc 0).1 (hc 0).2 f₁' f₂' hvac φ f hφ hf
        (ht 0) (g * a') (mul_mem hg0 (hE a' ha)) (h₁ * x) (mul_mem hh₁0 hx0) (h₂ * y) (mul_mem hh₂0 hy0)
      exact ⟨u, fun _ => ⟨fun x₀ => cv2 _ _ (hu1 x₀), cv1 _ _ hu2⟩⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose u hu using hV

  have hK : ∀ x₀ y₀, integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x * (Q 0).gl₁ x₀) (y * (Q 0).gl₂ y₀) =
      ∑ a' ∈ E.support, E a' * Gf a' x₀ y₀ := by
    intro x₀ y₀
    simp only [Gf]
    unfold integrand
    simp only [List.ofFn_succ]
    rw [pcomb_conv_cons, comb_aconv_cons ψ _ _ _ _ or₁, comb_aconv_cons ψ _ _ _ _ or₂, pcomb_eq_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    congr 1
    rw [pcomb_mapDomain]
    refine pcomb_congr _ fun a _ => ?_
    rw [hcomm a b (hE b hb), hf₁', hf₂']
    simp only [mul_assoc]
  have hI : innerVal Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y = ∑ a' ∈ E.support, E a' * Z a' := by
    simp only [Z]
    unfold innerVal integrand
    simp only [pcomb_eq_sum, Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  refine ⟨fun x₀ => ∑ a' ∈ E.support, E a' * u a' x₀, ?_, fun x₀ => ?_⟩
  · rw [hI]
    exact quotient_integral_fsum E.support (fun a' x₀ => E a' * u a' x₀) (fun a' => E a' * Z a')
      fun a' ha => ((hu a' ha).2.smul (E a'))
  · simp only [hK]
    exact quotient_integral_fsum E.support (fun a' y₀ => E a' * Gf a' x₀ y₀) (fun a' => E a' * u a' x₀)
      fun a' ha => (((hu a' ha).1 x₀).smul (E a'))

end GlobalTheory.QValInner

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselSecondStepFlatSupportRamified
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)

namespace GlobalTheory.FinPl

theorem suppSecond_holds : ∀ D : D7, SuppSecond D := by
  intro D k _ _ _ _ ι p n n' n'' _ _ _ _ _ _ q ψ σ B J B' s₁ s₂ l vL Λ P a b a' sh sd₂ Φ₁ Φ₂ hΦ₁ hΦ₂
  have tameP : ∀ v, P v → Tame D v := fun v hv => (sh.good v hv).tame
  refine ⟨?_, fun h₁ hh₁ => ⟨?_, ?_⟩⟩
  · exact _root_.GlobalTheory.VacFixP.vac_fix_on D ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil Λ.L₁ Λ.L₂ P
      (fun v hv => ⟨(sh.good v hv).sdW, sd₂, tameP v hv, (sh.unr v hv).2.1, (sh.unr v hv).2.2⟩) Φ₂ hΦ₂
  · intro h₂ hh₂
    exact _root_.GlobalTheory.VacSecondPf.vac_second D ψ σ J B' s₂ Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ P (fun v hv => ⟨sh.adapt v hv, (sh.unr v hv).2⟩) Φ₂ hΦ₂
      h₁ hh₁ h₂ hh₂
  · intro g hg φ hφ h₂ hne
    have key := _root_.GlobalTheory.FinPl.placesToAdeles_all D B'.V Λ.L₂ P sd₂ (besGrp B'.d B'.o) h₂ ?_
    · exact key
    intro v hv
    obtain ⟨hv', hhv, h', hh', rfl⟩ := _root_.GlobalTheory.FinPl.decompAt D B'.V h₂ v
    refine ⟨hv', hhv, h', hh', rfl, ?_⟩
    have gd := sh.good v hv
    have ad := sh.adapt v hv
    have sdL₁ : IsSelfDualC J.W Λ.L₁ := gd.sdW

    have hΦ₂v : Vac ψ J.W B'.V Λ.L₁ Λ.L₂ (· = v) Φ₂ :=
      ((_root_.GlobalTheory.VacLoc.vac_loc D ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil Λ.L₁ Λ.L₂ sdL₁ sd₂ P tameP Φ₂).1.mp hΦ₂).2 v hv
    set f := s₂.om (h₁, h') Φ₂ with hfdef
    have hf : Vac ψ J.W B'.V Λ.L₁ Λ.L₂ (· = v) f :=
      (_root_.GlobalTheory.VacLoc.vac_loc D ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil Λ.L₁ Λ.L₂ sdL₁ sd₂ (· = v)
        (fun w hw => hw ▸ gd.tame) Φ₂).2.1 hΦ₂v h₁ (_root_.GlobalTheory.FinPl.grpOff_anti D J.W P (· = v) (fun w hw => hw ▸ hv) hh₁) h' hh'

    set Ξ₁ := flatBF s₁ (s₁.om (g, h₁) Φ₁) with hΞ₁def
    have hΞ₁P : Vac ψ B.V₀ J.W₀ Λ.M₀ Λ.M₁ P Ξ₁ :=
      ((_root_.GlobalTheory.FinPl.suppFirst_all D ψ (σ + 1) B J s₁ Λ.L₀ Λ.M₀ Λ.L₁ Λ.M₁ P (fun w hw => sh.good w hw)
        (fun w hw => (sh.unr w hw).1) sdL₁ Φ₁ hΦ₁).2 g hg).2 h₁ hh₁
    have hΞ₁ : Vac ψ B.V₀ J.W₀ Λ.M₀ Λ.M₁ (· = v) Ξ₁ :=
      ((_root_.GlobalTheory.VacLoc.vac_loc D ψ B.V₀ J.W₀ s₁.χV s₁.χW s₁.om₀ s₁.weil₀ Λ.M₀ Λ.M₁ gd.sdV₀ gd.sdW₀ P tameP Ξ₁).1.mp
        hΞ₁P).2 v hv

    have hom : s₂.om (h₁, hv' * h') Φ₂ = s₂.om (1, hv') f := by
      rw [hfdef, show ((h₁, hv' * h') : GA D J.W × GA D B'.V) = (1, hv') * (h₁, h') by simp, map_mul]
      rfl
    have hand_eq : Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ (hv' * h') =
        hand0 s₁ s₂ l vL φ Ξ₁ (flatFB s₂ (s₂.om (1, hv') f)) := by
      simp only [Chain.hand, hand0, hom, hΞ₁def]
    rw [hand_eq] at hne
    have hne' : flatFB s₂ (s₂.om (1, hv') f) ≠ 0 := by
      intro h0
      apply hne
      rw [h0, show (0 : WO J.W₀ B'.V₀ → ℂ) = (0 : ℂ) • (0 : WO J.W₀ B'.V₀ → ℂ) by simp, _root_.GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel, zero_smul]
    obtain ⟨nn, hnF, hnv, γ, hγ, κ, hκ, hdec, hγp⟩ :=
      (_root_.GlobalTheory.FinPl.supportShift D ψ σ J B' s₂ Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ v ad (sh.unr v hv).2 (flatFB s₂)
        ((_root_.GlobalTheory.FinPl.flatLaws_all D ψ (· = v)).2 σ J B' s₂) ((_root_.GlobalTheory.FlatShiftPf.flatShift D ψ (· = v)).2 σ J B' s₂) f hf).2 hv' hhv hne'
    by_cases hgl : ∃ i, v = (p i).v
    · obtain ⟨i, rfl⟩ := hgl
      rcases GlobalTheory.T.threeOrbits_gluedCore_atPlace D k (p i) n'' q σ B' Λ.M₂ (a'.α i) (a'.α₀ i) (a'.P i) ad.sdW₀ (sh.gl' i) γ hγ hγp with
        ⟨a₀, ha₀, κ₀, hκ₀, rfl⟩ | ⟨Λ₀, hΛ₀, hmov⟩
      · obtain ⟨r, hr, hrv, κ', hκ', heq⟩ :=
          _root_.GlobalTheory.FinPl.OrbitCoset.orbit_coset D σ B' Λ.L₂ Λ.M₂ (p i).v ad.monoW nn hnF hnv a₀ ha₀ κ₀ hκ₀ κ hκ
        exact ⟨r, hr, hrv, κ', hκ', hdec.trans heq⟩
      · exfalso
        apply hne
        obtain ⟨M, sdM, hMov, hvacM⟩ :=
          _root_.GlobalTheory.FinPl.movedVac D ψ σ J B' s₂ Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ (p i).v ad (sh.unr _ hv).2 f hf γ hγ
        have hlat : (a'.α₀ i).IsLat M (lastKer Λ₀) ∨ (a'.α₀ i).IsLat M (lastPair q Λ₀).lat := by
          rcases hmov with h | h
          · exact Or.inl (_root_.GlobalTheory.FinPl.Frame.isLat_of_isLatMoved D k (p i) B'.V₀ (n'' ⊕ Fin 1) (a'.α₀ i) γ Λ.M₂ M _ hMov h)
          · exact Or.inr (_root_.GlobalTheory.FinPl.Frame.isLat_of_isLatMoved D k (p i) B'.V₀ (n'' ⊕ Fin 1) (a'.α₀ i) γ Λ.M₂ M _ hMov h)
        obtain ⟨φf, hφf, hφP⟩ := hφ.2 i
        have hz := GlobalTheory.T.gluedPlace_doubleStep_vanish_targetCoreLattice D k (p i) n n' n'' q ψ σ B J B' s₁ s₂ l vL s₂.weil.std (sh.unr _ hv).1
          (sh.unr _ hv).2 Λ.M₀ Λ.M₁ M (a.α i) (a.α₀ i) (b.β i) (a'.α i) (a'.α₀ i) (a.P i) (b.Q i) Λ₀ gd.sdV₀ gd.sdW₀
          sdM (sh.gl i) (sh.mid i) (sh.gl' i).sum hlat Ξ₁ _ hΞ₁ hvacM φf hφf
        rw [hφP] at hz
        rw [hdec, _root_.GlobalTheory.FinPl.flatFB_om_shift D ψ σ J B' s₂ Λ.L₁ Λ.L₂ (p i).v sdL₁ sd₂ gd.tame (sh.unr _ hv).2 f hf nn hnF hnv _ κ hκ,
          _root_.GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel, hz, smul_zero]
    · obtain ⟨a₀, ha₀, κ₀, hκ₀, rfl⟩ := _root_.GlobalTheory.FinPl.SplitOrbit.orbitSplit D σ B' Λ.M₂ v gd.tame ad.sdW₀
        (sh.split v hv fun i h => hgl ⟨i, h⟩) γ hγ hγp
      obtain ⟨r, hr, hrv, κ', hκ', heq⟩ := _root_.GlobalTheory.FinPl.OrbitCoset.orbit_coset D σ B' Λ.L₂ Λ.M₂ v ad.monoW nn hnF hnv a₀ ha₀ κ₀ hκ₀ κ hκ
      exact ⟨r, hr, hrv, κ', hκ', hdec.trans heq⟩

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralAdelesSplitPlacesIffHalves
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPl.SplitHalves

variable {D : D7}

theorem sum_idem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → SplitPt D k} {I : List ι} {P : Pl D → Prop} [DecidableEq ι] (hP : Places p I P) :
    ∑ i ∈ I.toFinset, GlobalTheory.FinPlLoc.idem D (· = (p i).v) = GlobalTheory.FinPlLoc.idem D P := by
  classical
  rw [← sub_eq_zero]
  apply GlobalTheory.FinPlLoc.eq_zero_of_comp
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [GlobalTheory.FinPlLoc.idem, GlobalTheory.FinPlLoc.infPart_pair, Finset.sum_const_zero, sub_zero]
  · intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [GlobalTheory.FinPlLoc.compAt_idem]
    by_cases hw : P w
    · obtain ⟨j, rfl⟩ := (hP.mem w).1 hw
      rw [Finset.sum_eq_single j (fun i _ hij => if_neg (fun h => hij (hP.inj h.symm)))
        (fun hj => absurd (List.mem_toFinset.2 (hP.all j)) hj), if_pos rfl, if_pos hw, sub_self]
    · rw [Finset.sum_eq_zero (fun i _ => if_neg (fun h => hw ((hP.mem w).2 ⟨i, h⟩))), if_neg hw, sub_self]

theorem mem_intAt_iff_halves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ a : AE D, a ∈ intAt D P ↔ a ∈ idAt D P ∧ ∀ i, (p i).pr a ∈ 𝒪[k] ∧ (p i).pr (cA D a) ∈ 𝒪[k] := by
  intro D k _ _ _ _ ι p I P hP a
  classical
  have hpr (q : SplitPt D k) (c : k) : q.pr (cA D (q.sec c)) = 0 := by
    have he : q.pr q.e = 1 := by rw [← GlobalTheory.FinPl.FrameLat.sec_one, q.pr_sec]
    have h0 : q.e * cA D (q.sec c) = 0 := by
      rw [← cA_cA q.e, ← map_mul, ← GlobalTheory.FinPl.FrameLat.e_mul_sec q c,
        ← mul_assoc, GlobalTheory.FinPl.FrameLat.cAe_mul_e, zero_mul, map_zero]
    have h1 := congrArg q.pr h0
    rwa [RingHom.map_mul, he, one_mul, RingHom.map_zero] at h1
  have hs (q : SplitPt D k) (a : AE D) (t : k) :
      a * q.sec t ∈ intAt D (· = q.v) ↔ q.pr a * t ∈ 𝒪[k] := by
    rw [mul_comm, GlobalTheory.FinPl.FrameLat.sec_mul_right,
      GlobalTheory.SeeSaw.CoreGlue.mem_intAt_iff q (GlobalTheory.FinPl.FrameLat.sec_mem_idAt q _),
      hpr, q.pr_sec, and_iff_left (zero_mem _), mul_comm]
  have hcs (q : SplitPt D k) (a : AE D) (t : k) :
      a * cA D (q.sec t) ∈ intAt D (· = q.v) ↔ q.pr (cA D a) * t ∈ 𝒪[k] := by
    have hm : cA D (q.sec t) * a = cA D (q.sec (t * q.pr (cA D a))) := by
      rw [← GlobalTheory.FinPl.FrameLat.sec_mul_right, RingHom.map_mul, GlobalTheory.SeeSaw.cA_cA]
    rw [mul_comm, hm, GlobalTheory.SeeSaw.CoreGlue.mem_intAt_iff q
      (GlobalTheory.FinPl.FrameLat.csec_mem_idAt _), hpr, GlobalTheory.SeeSaw.cA_cA, q.pr_sec,
      and_iff_right (zero_mem _), mul_comm]
  have hsec1 : ∀ i, (p i).sec 1 ∈ intAt D (· = (p i).v) := fun i => by
    simpa using (hs (p i) 1 1).2 (by simp)
  have hcsec1 : ∀ i, cA D ((p i).sec 1) ∈ intAt D (· = (p i).v) := fun i => by
    simpa using (hcs (p i) 1 1).2 (by simp)
  constructor
  · intro h
    have hr := (GlobalTheory.IwaIdeals.mem_intAt_iff.1 h).2
    refine ⟨h.1, fun i => ⟨?_, ?_⟩⟩
    · have h1 : a * (p i).sec 1 ∈ intAt D (· = (p i).v) := GlobalTheory.IwaIdeals.mem_intAt_iff.2
        ⟨Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.sec_mem_idAt _ _),
          mul_mem hr (GlobalTheory.IwaIdeals.mem_intAt_iff.1 (hsec1 i)).2⟩
      simpa using (hs (p i) a 1).1 h1
    · have h1 : a * cA D ((p i).sec 1) ∈ intAt D (· = (p i).v) := GlobalTheory.IwaIdeals.mem_intAt_iff.2
        ⟨Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.csec_mem_idAt (p := p i) 1),
          mul_mem hr (GlobalTheory.IwaIdeals.mem_intAt_iff.1 (hcsec1 i)).2⟩
      simpa using (hcs (p i) a 1).1 h1
  · rintro ⟨hid, hh⟩
    refine ⟨hid, ?_⟩
    have ha : a = ∑ i ∈ I.toFinset, (a * (p i).sec 1 + a * cA D ((p i).sec 1)) := by
      conv_lhs => rw [← (GlobalTheory.FinPlLoc.mem_idAt_iff P a).1 hid, ← sum_idem hP, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      set ε := GlobalTheory.FinPlLoc.idem D (· = (p i).v)
      have h1 : ε * a ∈ idAt D (· = (p i).v) := Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
      have h2 := (GlobalTheory.FinPl.FrameLat.idem_iff (p i) _).1 h1
      have he : ε * (p i).sec 1 = (p i).sec 1 :=
        (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.sec_mem_idAt _ _)
      have hce : ε * cA D ((p i).sec 1) = cA D ((p i).sec 1) :=
        (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.csec_mem_idAt (p := p i) 1)
      rw [GlobalTheory.FinPl.FrameLat.sec_one] at he hce ⊢
      calc ε * a = ((p i).e + cA D (p i).e) * (ε * a) := h2.symm
        _ = (ε * (p i).e) * a + (ε * cA D (p i).e) * a := by
          rw [add_mul, mul_left_comm, ← mul_assoc, mul_left_comm (cA D (p i).e), ← mul_assoc]
        _ = a * (p i).e + a * cA D (p i).e := by rw [he, hce, mul_comm (p i).e, mul_comm (cA D (p i).e)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ha, map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [map_add (f := _)]
    exact add_mem ((hs (p i) a 1).2 (by simpa using (hh i).1)).2
      ((hcs (p i) a 1).2 (by simpa using (hh i).2)).2

end GlobalTheory.FinPl.SplitHalves

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceFinitelyManyCellsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_twistPlace_finitely_many_cells : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) (a : GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∃ T : Finset (GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k), ∀ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ → ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v), ∀ x, flatBF (t.sBF j (σ + 1) h) (t.om j (g * (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a, h₁ * (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) x) (comb c.ψ _ _ ((F.Q i).eL j) f₁)) ≠ 0 → ∃ τ ∈ T, ∃ r, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧ ∃ κ ∈ ((F.Q i).T.lev (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega)).J, x = r * τ * κ := by
  first | exact @GlobalTheory.QFinOneAt.finOne_pin | exact GlobalTheory.QFinOneAt.finOne_pin | (intros; apply GlobalTheory.QFinOneAt.finOne_pin <;> assumption)
end

