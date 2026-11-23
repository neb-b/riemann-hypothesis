module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PromodularityCaseThreeOfLemmas
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Cu
private theorem chain_rank_four_good {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] {Φ : Fr O Γ} {a : O →+* R} {P : PD Φ.ι Γ R}
    [TopologicalSpace Γ] {P' : PD Φ.ι Γ R} (hP : Φ.IsRes a P) (h : Chain4 Φ a P P') :
    Φ.IsRes a P' ∧ Good4 Φ a P' := by
  obtain ⟨hg, hc⟩ := h
  induction hc with
  | refl => exact ⟨hP, hg⟩
  | tail _ hl _ => exact ⟨Asm.linked_isRes hl.2, hl.1⟩
private theorem allIn_of_chain4 {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} {l : ℕ} [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ} (hΦ : Φ.Std l a)
    (X : Space Φ a) (J : Ideal X.B)
    (hch : ∀ x : X.A →ₐ[Λ] ResidueField Λ, Φ.IsRes ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) →
      Good4 Φ ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) → X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x))
    (x₀ x₁ : X.A →ₐ[Λ] ResidueField Λ) (hs : Φ.IsRes ((residue Λ).comp a) (X.P.map (x₀ : X.A →+* ResidueField Λ)))
    (hc : Chain4 Φ ((residue Λ).comp a) (X.P.map (x₀ : X.A →+* ResidueField Λ)) (X.P.map (x₁ : X.A →+* ResidueField Λ)))
    (h₁ : X.SomeIn J (RingHom.ker x₁)) : X.AllIn J (RingHom.ker x₀) := by
  have key : ∀ s, Relation.ReflTransGen (fun x y => Good4 Φ ((residue Λ).comp a) y ∧ Φ.Linked ((residue Λ).comp a) x y) s
      (X.P.map (x₁ : X.A →+* ResidueField Λ)) → Φ.IsRes ((residue Λ).comp a) s → Good4 Φ ((residue Λ).comp a) s →
      ∀ x : X.A →ₐ[Λ] ResidueField Λ, X.P.map (x : X.A →+* ResidueField Λ) = s → X.AllIn J (RingHom.ker x) := by
    intro s h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro k1 k2 x e
      refine hch x (e ▸ k1) (e ▸ k2) ((conn Φ l a hΦ X J x x₁ ?_).2 (hch x₁ k1 k2 h₁))
      rw [e]
      exact Asm.linked_self k1
    | head hl _ ih =>
      rintro k1 k2 x rfl
      obtain ⟨x', rfl⟩ := Asm.end_pt X hl.2
      exact hch x k1 k2 ((conn Φ l a hΦ X J x x' hl.2).2 (ih (Asm.linked_isRes hl.2) hl.1 x' rfl))
  exact key _ hc.2 hs hc.1 x₀ rfl
private theorem conj_trans {H R : Type} [Group H] [CommRing R] {r r' r'' : H →* M4 R} (h : IsConj4 r r') (h' : IsConj4 r' r'') :
    IsConj4 r r'' := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := h'
  exact ⟨v * u, fun g => by rw [hv, hu, mul_inv_rev, Units.val_mul, Units.val_mul]; simp only [mul_assoc]⟩
private theorem res_self (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] :
    (res O O : O →+* ResidueField O) = residue O := RingHom.ext fun x => (res O O).commutes x
private theorem last_step (hCh : _root_.UpperTheory.V.Cu.ChainRankFour) (hCD : ChainDesc4) (hC : CohomologyHyp) (hPM : _root_.UpperTheory.V.Ws.PMExAlt) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} {D : Raw Ω c} (T : Tower D) (hF : T.Fit) (hD : T.Deep) (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (C : ℕ)
    (hB : ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → (T.fr ∅).Bounds a T.d C)
    (hd : 30 * (C + 1) * (C + 1) ≤ T.d) {c₁ : Coef l} {h₁ : c.O ≤ c₁.O} {Q : PD T.ι (G T.F Ω) c₁.O} (hQ : T.SeedPairAlt ι h₁ Q)
    {P : PD T.ι (G T.F Ω) 𝔞.V} (hs : 𝔞.Small P) (hp : (T.fr ∅).IsPair (𝔞.a c) P)
    (hr : (T.fr ∅).IsRes (𝔞.red c) (P.map (residue 𝔞.V)))
    (hch : Chain4 (T.fr ∅) (𝔞.red c) (P.map (residue 𝔞.V)) (Q.map (𝔞.red c₁))) :
    ∃ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B) (y : X.A →+* 𝔞.V), T.PotentialModularityTower ι X J ∧
      y.comp (algebraMap c'.O X.A) = 𝔞.a c' ∧ (∀ b ∈ maximalIdeal X.B, y (algebraMap X.B X.A b) ∈ maximalIdeal 𝔞.V) ∧
      (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) ∧ X.P.map y = P := by
  obtain ⟨c₂, k₂⟩ := hCD 𝔞 c (T.fr ∅) _ _ hr hch
  obtain ⟨c₃, k₃⟩ := smallCo 𝔞 P hs
  obtain ⟨c₄, k₄⟩ := hPM Ω l c D T hF hD ι
  obtain ⟨d₁, a₁, a₂⟩ := (coefSup l).1 c₁ c₂
  obtain ⟨d₂, a₃, a₄⟩ := (coefSup l).1 c₃ c₄
  obtain ⟨c', b₁, b₂⟩ := (coefSup l).1 d₁ d₂
  have e₁ : c₁.O ≤ c'.O := a₁.trans b₁
  have h : c.O ≤ c'.O := h₁.trans e₁
  haveI : Finite (ResidueField c'.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c'.O) := (dvrFacts l c'.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  have hS := (std hC D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  obtain ⟨X⟩ := spaceEx (T.fr ∅) l (inc h) hS
  obtain ⟨J, hJ⟩ := k₄ c' h (a₄.trans b₂) X
  obtain ⟨s, t, es, et, rs, cst⟩ := k₂ c' h (a₂.trans b₁)
  obtain ⟨R, _, _, _, f, QR, fi, fa, fr, qc, rfl⟩ := k₃ c' (a₃.trans b₂)
  have inj := (chainMap (T.fr ∅) ((residue c'.O).comp (inc h)) (𝔞.j c') s).2.2
  have loc : ∀ {d : Coef l} (e : d.O ≤ c'.O), maximalIdeal d.O ≤ (maximalIdeal c'.O).comap (inc e) := fun {d} e x hx hu => by
    have h2 : IsUnit (𝔞.a d x) := 𝔞.compat d c' e x ▸ hu.map (𝔞.a c')
    exact hx (IsLocalHom.map_nonunit x h2)
  have jc : (𝔞.j c').comp ((residue c'.O).comp (inc e₁)) = 𝔞.red c₁ :=
    RingHom.ext fun x => congrArg (residue 𝔞.V) (𝔞.compat c₁ c' e₁ x)
  have lQ : (T.fr ∅).Lifts (inc h) t (Q.map (inc e₁)) := by
    refine ⟨hQ.pair.map (inc e₁), hQ.cont.map _ (loc e₁), inj ?_⟩
    show ((Q.map _).map _).map _ = t.map _
    rw [et, res_self, PD.map_map, PD.map_map, ← jc]
    rfl
  obtain ⟨f₁, hf₁⟩ := X.univ c'.O t _ (chain_rank_four_good rs cst).1 lQ
  have sd := hJ.seed ((Algebra.ofId c'.O (PadicAlgCl l)).comp f₁) (by
    have e : X.P.map (((Algebra.ofId c'.O (PadicAlgCl l)).comp f₁ : X.A →ₐ[c'.O] PadicAlgCl l) : X.A →+* PadicAlgCl l) =
        Q.map (algebraMap c₁.O (PadicAlgCl l)) := by
      show (X.P.map (f₁ : X.A →+* c'.O)).map (algebraMap c'.O (PadicAlgCl l)) = _
      rw [hf₁]
      rfl
    rw [e]
    exact hQ.seed)
  have s₁ : X.SomeIn J (RingHom.ker ((res c'.O c'.O).comp f₁)) := Asm.someIn_of_locZero X J _ sd fun z hz => by
    have h0 : f₁ z = 0 := Subtype.ext hz
    show res c'.O c'.O (f₁ z) = 0
    rw [h0, map_zero]
  have e₁' : X.P.map (((res c'.O c'.O).comp f₁ : X.A →ₐ[c'.O] ResidueField c'.O) : X.A →+* ResidueField c'.O) = t := by
    show (X.P.map (f₁ : X.A →+* c'.O)).map (res c'.O c'.O : c'.O →+* ResidueField c'.O) = t
    rw [hf₁]
    exact lQ.red
  have lR : (T.fr ∅).Lifts (inc h) s QR := by
    refine ⟨Asm.pair_of f fi ?_, qc, inj ?_⟩
    · rw [← RingHom.comp_assoc, fa]
      have : (𝔞.a c').comp (inc h) = 𝔞.a c := RingHom.ext fun x => 𝔞.compat c c' h x
      rw [this]
      exact hp
    · show (QR.map _).map _ = s.map _
      rw [es, PD.map_map, PD.map_map, fr]
  obtain ⟨f₀, hf₀⟩ := X.univ R s _ rs lR
  have e₀ : X.P.map (((res c'.O R).comp f₀ : X.A →ₐ[c'.O] ResidueField c'.O) : X.A →+* ResidueField c'.O) = s := by
    show (X.P.map (f₀ : X.A →+* R)).map (res c'.O R : R →+* ResidueField c'.O) = s
    rw [hf₀]
    exact lR.red
  have all := allIn_of_chain4 hS X J
    (hCh hC D T hF hD ι c' h X J hJ C (hB _ _ fun x hx => (residue_eq_zero_iff _).2 (loc h hx)) hd)
    ((res c'.O R).comp f₀) ((res c'.O c'.O).comp f₁) (e₀ ▸ rs) (e₀ ▸ e₁' ▸ cst) s₁
  refine ⟨c', h, X, J, f.comp (f₀ : X.A →+* R), hJ, ?_, fun b hb => ?_, Asm.zero_of_allIn X J _ all fun z hz => ?_, ?_⟩
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, fa]
  · have h0 : res c'.O R ((f₀.comp (IsScalarTower.toAlgHom c'.O X.B X.A)) b) = 0 := by
      rw [res_map, res_eq_zero_iff]
      exact hb
    refine (residue_eq_zero_iff _).1 ((RingHom.congr_fun fr (f₀ (algebraMap X.B X.A b))).trans ?_)
    exact (congrArg (𝔞.j c') h0).trans (map_zero _)
  · have h0 : f₀ z = 0 := (map_eq_zero_iff f fi).1 hz
    show res c'.O R (f₀ z) = 0
    rw [h0, map_zero]
  · exact congrArg (fun Z => PD.map Z f) hf₀
theorem UpperTheory.V.Cu.promodularity_case_three_of_chain_reduction : ExistsTensorFactorTower → _root_.UpperTheory.V.Cu.ChainRankFour → ChainDesc4 → _root_.UpperTheory.V.Cu.RankFourChainReductionDense → _root_.UpperTheory.V.Cu.PromodularityCaseThreeDense := by
  intro hLem hCh hCD hCIV hC hFW hH h4 hPM Ω _ _ _ l _ c D hD ι 𝔞 r u hK hS
  have hG : D.Good := hD.1
  obtain ⟨pr, hl, hP⟩ := labels D hG 𝔞 r u hK
  obtain ⟨T₀, rfl, ok, four, tame₀⟩ := hLem D hD pr hl
  have hF₀ : T₀.Fit := hH D T₀ hD ok four
  have hc := hCIV hC hH h4 D T₀ hD ok four tame₀ ι 𝔞
  obtain ⟨P, qP, nP, cP, sP⟩ := hP _ hF₀.1.dist
  obtain ⟨P', qP', cP', lP'⟩ := lat hC D hG 𝔞 _ _ hl hF₀.1.dist P qP nP (sP hS)
  obtain ⟨T₁, le₁, tame, hT⟩ := hc _ lP'
  have f₁ := leFit D hG T₀ T₁ le₁
  have hF₁ := f₁.2.2.2.2.1 hF₀
  obtain ⟨C, hB⟩ := x2 hC hFW D T₁ hF₁ tame
  obtain ⟨T, m, le, lay, deep, hd⟩ := layerEx D hG T₁ hF₁ tame (30 * (C + 1) * (C + 1))
  have hF := (leFit D hG T₁ T le).2.2.2.2.1 hF₁
  obtain ⟨c₁, h₁, Q, hQ, hch⟩ := hT T le deep
  obtain ⟨P'', sm, pr'', er, ov, rs, ine⟩ := restrQ D hG T₀ T hF₀ (f₁.2.2.2.2.2.2 T le) 𝔞 P' qP' lP'
  obtain ⟨c', h, X, J, y, k1, k2, k3, k4, k5⟩ :=
    last_step hCh hCD hC hPM T hF deep ι 𝔞 C (hB T m le lay) hd hQ sm pr'' rs (hch _ ov rs)
  refine ⟨T, c', h, X, J, y, P'.r, hF, deep, k1, k2, k3, k4, conj_trans cP cP', qP'.pair.mult, by rw [k5, er],
    fun v i s hs => ?_⟩
  subst k5
  exact (PD.map_ψ X.P y v i s).symm.trans (ine v i s hs)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAtSame
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
private theorem ev_of_gen {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (μ a : ℂ) (F : M) (hF : F ≠ 0)
    (h : F ∈ T.maxGenEigenspace μ) (ha : T F = a • F) : a = μ := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T μ F).1 h
  have h1 : ∀ j : ℕ, ((T - μ • 1) ^ j) F = (a - μ) ^ j • F := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, ha]
      simp only [LinearMap.smul_apply, Module.End.one_apply]
      rw [← sub_smul, smul_smul, pow_succ]
  rw [h1 k] at hk
  have h2 := (smul_eq_zero.1 hk).resolve_right hF
  by_contra hne
  exact pow_ne_zero k (sub_ne_zero.2 hne) h2
private theorem sat_eq (n q : ℕ) (hq : q ≠ 0) (B B' : Multiset ℂˣ) (a a' : ℕ → ℂ) (haa : ∀ j ≤ n, a j = a' j)
    (h : ((UpperTheory.V.Af.algSat n q B).map fun b => X - C b).prod = heckePol n q a)
    (h' : ((UpperTheory.V.Af.algSat n q B').map fun b => X - C b).prod = heckePol n q a') : B = B' := by
  have hp : heckePol n q a = heckePol n q a' := by
    rw [UpperTheory.V.Hi.heckePol, UpperTheory.V.Hi.heckePol]
    exact Finset.sum_congr rfl fun j hj => by rw [haa j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  have hr : UpperTheory.V.Af.algSat n q B = UpperTheory.V.Af.algSat n q B' := by
    rw [← Polynomial.roots_multiset_prod_X_sub_C (UpperTheory.V.Af.algSat n q B), h, hp, ← h',
      Polynomial.roots_multiset_prod_X_sub_C]
  have hc : ((((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq
    exact_mod_cast (Real.rpow_pos_of_pos this _).ne'
  unfold UpperTheory.V.Af.algSat at hr
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map] at hr
  exact Multiset.map_injective (fun x y hxy => Units.ext (mul_left_cancel₀ hc hxy)) hr
private theorem mem_gen {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ)
    (x : A →+* Qbar l) (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) (K : H.Lev) (b : ℕ) (ev : H.Op → ℂ) (i : H.Op)
    (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ zPart H θ ι x lam ξ K b ev) : F ∈ (H.opC ι lam d i).maxGenEigenspace (ev i) :=
  (Submodule.mem_iInf _).1 hF.2 i
private theorem vals (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hξ : IsBasis ι e ξ) (Z : Submodule ℂ (Fin m → (hset Q τ₀).X.Fn ℂ d))
    (ev : (hset Q τ₀).Op → ℂ) (hZ : ∀ i, ∀ F ∈ Z, F ∈ ((hset Q τ₀).opC ι lam d i).maxGenEigenspace (ev i))
    (σ : Submodule ℂ (UA L n → ℂ)) (hσ : IsAutRepU σ) (hY : YOf Q ι τ₀ e ξ σ ⊓ Z ≠ ⊥)
    (w : (hset Q τ₀).Wp) (τ : SmIrr (GLw n w.1)) (hτ : Cp σ w.1 τ) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w.1 τ.ρ B) :
    ∃ a : ℕ → ℂ, a 0 = 1 ∧ (∀ j : Fin n, a (j + 1) = ev (.inl (w, j))) ∧
      ((UpperTheory.V.Af.algSat n (normV w.1) B).map fun b => X - C b).prod = heckePol n (normV w.1) a := by
  obtain ⟨-, a, ha0, ha, hp⟩ := satT L n w.1 τ B hB
  refine ⟨a, ha0, fun j => ?_, hp⟩
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  have hAx : (hset Q τ₀).Ax := _root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V Q c m τ₀
  have h1 := partUR2Sph l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ hAx w.1 w.2.1 w.2.2 τ hτ (j + 1) _ (ha (j + 1)) F hF.1
  exact ev_of_gen _ _ _ F hF0 (hZ (.inl (w, j)) F hF.2) h1
theorem atSame_alt : _root_.UpperTheory.V.Z.J.D.AtSameAlt := by
  intro hN l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ A _ _ _ θ x c0 sp hWt hSp K ev σ σ' hσ hσ' h1 h2 π hπ
  have hZ := fun i F hF => mem_gen (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev i F hF
  have hY' : YOf Q ι τ₀ e ξ σ' ≠ ⊥ := fun h => h2 (eq_bot_iff.2 (inf_le_left.trans h.le))
  have hU := partUR2Unr l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ σ' hσ' hY'
  have hfin : ∀ᶠ w : Plc L in cofinite, w.under (𝓞 (Lp L)) ∉ V.S' :=
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under (Lp L) L).eventually V.fin.compl_mem_cofinite
  refine (hπ.and hfin).mono ?_
  rintro w ⟨hw, hS⟩ hsp
  obtain ⟨τ, B, hτ, hB, hs⟩ := hw hsp
  obtain ⟨τ', -, h1', h2'⟩ := GlobalTheory.DefU.exists_locComp_split L n ⟨σ', hσ'⟩ w hsp
  obtain ⟨B', hB'⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible τ'.smooth τ'.irred (h2'.1 (hU w hS))
  let w' : (hset Q τ₀).Wp := ⟨w, hS, hsp⟩
  obtain ⟨a, a0, ha, hp⟩ := vals hN s n hn V Q c ι m τ₀ lam d e ξ hξ _ ev hZ σ hσ h1 w' τ hτ B hB
  obtain ⟨a', a0', ha', hp'⟩ := vals hN s n hn V Q c ι m τ₀ lam d e ξ hξ _ ev hZ σ' hσ' h2 w' τ' h1' B' hB'
  have hq : normV w ≠ 0 := by
    have : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
    exact Nat.card_pos.ne'
  have hBB := sat_eq n (normV w) hq B B' a a' (fun j hj => by
    rcases j with _ | j
    · rw [a0, a0']
    · have := ha ⟨j, hj⟩
      have h' := ha' ⟨j, hj⟩
      exact this.trans h'.symm) hp hp'
  subst hBB
  exact ⟨τ', B, h1', hB', hs⟩
end UpperTheory.V.Z.J.D
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPartRep
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
private theorem val_eq {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {F : M} (h0 : F ≠ 0) {a b : ℂ}
    (h : T F = a • F) (hg : F ∈ T.maxGenEigenspace b) : a = b := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T b F).1 hg
  have hp : ∀ k : ℕ, ((T - b • (1 : Module.End ℂ M)) ^ k) F = (a - b) ^ k • F := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h, LinearMap.smul_apply,
        Module.End.one_apply, ← sub_smul, smul_smul, pow_succ]
  rw [hp k] at hk
  rcases smul_eq_zero.1 hk with h1 | h1
  · exact sub_eq_zero.1 (by_contra fun h2 => pow_ne_zero k h2 h1)
  · exact absurd h1 h0
private theorem chi_map {n : ℕ} {R S G : Type} [CommRing R] [CommRing S] [Group G] (D : W.GDet n R G) (f : R →+* S) (g : G) :
    (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  letI : Algebra R (Polynomial S) := ((algebraMap S (Polynomial S)).comp f).toAlgebra
  let φ : Polynomial R →ₐ[R] Polynomial S :=
    { Polynomial.mapRingHom f with commutes' := fun b => Polynomial.map_C f }
  refine Eq.trans ?_ (D.nat (Polynomial R) (Polynomial S) φ
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1)))
  change D.D (Polynomial S) _ = D.D (Polynomial S) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
  congr 1
  simp [map_sub, MonoidAlgebra.mapRingHom_single]
private theorem pol_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n q : ℕ) (a : ℕ → R) (b : ℕ → S)
    (h : ∀ j ≤ n, f (a j) = b j) : (Hi.heckePol n q a).map f = Hi.heckePol n q b := by
  unfold Hi.heckePol
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, map_mul, h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  simp
private theorem ss_irr {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} (h : Af.IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp
theorem partRep_s : _root_.UpperTheory.V.Z.J.D.PartRepAlt := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ _ ι x lam d ξ c0 sp _ K a _ _ _ z _ I D ψ hU ρ hρ hirr hD Y hY
  obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
  have hgen : ∀ i, F ∈ (H.opC ι lam d i).maxGenEigenspace (ι (z (H.gen θ a K i))) := fun i =>
    (Submodule.mem_iInf _).1 hF.2.2 i
  have hval : ∀ (w : H.Wp) (j : ℕ), j ≤ n → ι (z (H.genW θ a K w j)) = Y.a w j := by
    intro w j hj
    unfold HSet.genW
    split_ifs with h
    · have e := Y.sph w (j - 1 + 1) F hF.1
      rw [show j - 1 + 1 = j by omega] at e
      have e' : H.opC ι lam d (.inl (w, ⟨j - 1, h.2⟩)) F = Y.a w j • F := by
        have e2 : H.opC ι lam d (.inl (w, ⟨j - 1, h.2⟩)) F = sphOp (H.atW ι d w.1) (j - 1 + 1) F := rfl
        rw [e2, show j - 1 + 1 = j by omega, e]
      exact (val_eq _ hF0 e' (hgen _)).symm
    · rw [show j = 0 by omega, Y.a_zero, map_one, map_one]
  have e : W.GDet.ofRep (W.mat Y.r) = W.GDet.ofRep (W.mat ρ) := by
    refine AlgebraTools.Det.extDense _ _ _ hH.dense (fun i _ => AlgebraTools.Det.repCont _ (Units.continuous_val.comp Y.cont) i)
      (fun i _ => AlgebraTools.Det.repCont _ (Units.continuous_val.comp hρ) i) ?_
    rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    rw [← hD, chi_map, hU.frob ⟨w, hw⟩ B σ hB hσ, (AlgebraTools.Det.repApi _).2.1]
    refine Polynomial.map_injective ι.toRingHom ι.injective ?_
    refine (Y.frob ⟨w, hw⟩ B σ hB hσ).trans ?_
    rw [Polynomial.map_map]
    exact (pol_map _ n _ _ _ fun j hj => hval ⟨w, hw⟩ j hj).symm
  obtain ⟨P, hP⟩ := AlgebraTools.Det.bnRep (W.mat Y.r) (W.mat ρ) Y.ss (ss_irr hirr) fun g => by
    rw [← (AlgebraTools.Det.repApi (W.mat Y.r)).2.1 g, ← (AlgebraTools.Det.repApi (W.mat ρ)).2.1 g, e]
  refine ⟨P, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (hP g).symm
end UpperTheory.V.Z.J.D
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSphSame
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
private theorem lat {α : Type*} [Lattice α] {Y B f z E : α} (h1 : Y ≤ B) (h2 : Y ≤ f) (h3 : Y ≤ E) :
    Y ⊓ (B ⊓ f ⊓ z ⊓ E) = Y ⊓ z :=
  le_antisymm (le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_right)))
    (le_inf inf_le_left (le_inf (le_inf (le_inf (inf_le_left.trans h1) (inf_le_left.trans h2)) inf_le_right)
      (inf_le_left.trans h3)))
private theorem eig_eq {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {a b : ℂ} {F : M} (h0 : F ≠ 0)
    (hT : T F = a • F) (hF : F ∈ T.maxGenEigenspace b) : a = b := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T b F).1 hF
  have h1 : (T - b • (1 : Module.End ℂ M)) F = (a - b) • F := by
    simp [hT, sub_smul]
  have h : ∀ i : ℕ, ((T - b • (1 : Module.End ℂ M)) ^ i) F = (a - b) ^ i • F := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, pow_succ']
  rw [h k] at hk
  by_contra hne
  exact smul_ne_zero (pow_ne_zero k (sub_ne_zero.2 hne)) h0 hk
private theorem eig_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {b : ℂ} {F : M}
    (hT : T F = b • F) : F ∈ T.maxGenEigenspace b :=
  (Module.End.mem_maxGenEigenspace T b F).2 ⟨1, by simp [hT]⟩
private theorem eig_le {M I : Type*} [AddCommGroup M] [Module ℂ M] (T : I → Module.End ℂ M) (ev : I → ℂ) (i : I) (a : ℂ)
    (O Y Y' : Submodule ℂ M) (hne : Y ⊓ (O ⊓ ⨅ i, (T i).maxGenEigenspace (ev i)) ≠ ⊥)
    (h1 : ∀ F ∈ Y, T i F = a • F) (h2 : ∀ F ∈ Y', T i F = a • F) : Y' ≤ (T i).maxGenEigenspace (ev i) := by
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hFe : F ∈ (T i).maxGenEigenspace (ev i) :=
    (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hF).2).2 i
  have hae : a = ev i := eig_eq _ hF0 (h1 F (Submodule.mem_inf.1 hF).1) hFe
  intro F' hF'
  exact eig_mem _ (hae ▸ h2 F' hF')
private theorem scalar (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GLw n w)) (j : ℕ) :
    ∃ a : ℂ, ∀ v ∈ fixd τ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp τ.ρ j v = a • v := by
  by_cases h : GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL w (n := n))
  · obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible τ.smooth τ.irred h
    obtain ⟨-, a, -, ha, -⟩ := UpperTheory.V.Hi.satT L n w τ B hB
    exact ⟨a j, ha j⟩
  · refine ⟨0, fun v hv => ?_⟩
    have hv0 : v = 0 := by
      by_contra h0
      rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n] at hv
      exact h ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, h0⟩)
    simp [hv0]
theorem spherical_same_of_z_eq : ZEq → _root_.UpperTheory.V.Z.J.D.SphSameAlt := by
  intro hZ hLit l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hξ A _ _ _ θ x c0 sp hWt hSp K ev hev σ σ' hσ hσ' hcp hne
  have hAx := _root_.UpperTheory.V.Hi.axU_s hLit l L Ω s n hn V Q c m τ₀
  have hYB : YOf Q ι τ₀ e ξ σ' ≤ (hset Q τ₀).Big ι ξ := inf_le_left
  rw [hZ L Ω l n c (hset Q τ₀) hAx A θ hWt ι x lam d ξ c0 sp hSp K ev hev]
  refine lat hYB ?_ ?_
  · haveI : IsEmpty (hset Q τ₀).Q := ⟨fun q => Q.notS q (by
      have h : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
        rw [Q.range]
        exact Or.inr ⟨q, rfl⟩
      rwa [hV] at h)⟩
    have hl : (hset Q τ₀).lev K = (hset Q τ₀).UQ := by
      simp only [HSet.lev, iSup_of_empty]
      exact sup_bot_eq _
    rw [hl]
    exact hYB.trans inf_le_right
  · refine le_iInf fun p => ?_
    obtain ⟨τ, h1, h2⟩ := hcp p.1.1 p.1.2.2
    obtain ⟨a, ha⟩ := scalar L n p.1.1 τ ((p.2 : ℕ) + 1)
    have hs := fun (σ₁ : Submodule ℂ (UA L n → ℂ)) (hσ₁ : IsAutRepU σ₁) (hτ₁ : Cp σ₁ p.1.1 τ) =>
      UpperTheory.V.Hi.partUR2Sph l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ σ₁ hσ₁ hAx p.1.1 p.1.2.1 p.1.2.2 τ hτ₁ _ a ha
    exact eig_le ((hset Q τ₀).opC ι lam d) ev (.inl p) a ((hset Q τ₀).OrdAt θ ι x.toRingHom lam ξ K c0) _ _ hne
      (hs σ hσ h1) (hs σ' hσ' h2)
end UpperTheory.V.Z.J.D
end
end
end

