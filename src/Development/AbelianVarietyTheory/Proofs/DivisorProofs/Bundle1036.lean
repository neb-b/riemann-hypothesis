module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairRecordCore
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.RecPairCore
open GlobalTheory.AdTh.RecPair

theorem isPair_record_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0), VStd D i → IsPair R.ψ R.θ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 (R.ωP i t) ∧ (Vc D i).rank ≠ 0 ∧ (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = L0c D (Vc D i) ∧ (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = L0c D (Wc D i) ∧ IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank : Set (Fin (Vc D i).rank → D.host.E)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i t hV
  have hL := h.lev
  have hW := h.thP.ωP i t
  have hr : Odd D.R.r := by
    have := D.R.m_add_three_le_k
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hev : Even (Vc D i).rank := rV ▸ hr.add_odd D.R.t_odd
  have hη : GlobalTheory.WeilParts.IsEtaTilde D R.eta :=
    GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT (hev.add_odd (rW ▸ hr))
  have lV := coe_eq_of_frame (hL.βV i)
  have lW := coe_eq_of_frame (hL.βW i)
  refine ⟨⟨hW, h.models.inf, hV.1, hev, D.sp.V_sig _, D.sp.W_sig _, exp_mu hL i t, fun τ => ?_, fun v ε hv => ?_, ⟨_, hη⟩⟩,
    ?_, lV, lW, selfDual_of_coe lV, selfDual_of_coe lW, ?_⟩
  · obtain ⟨a, ha⟩ := exp_mu hL i t τ
    obtain ⟨s, hs⟩ := hr
    refine ⟨a - s - 1, ?_⟩
    have h3 := GlobalTheory.Mem.HeckeExp.hasInfExp_mul ha (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hη.2.2.2 τ))
    have e : ((a - s - 1 : ℤ) : ℚ) + ((Wc D i).rank : ℚ) / 2 = (a : ℚ) + -(1 / 2) := by
      rw [rW, hs]; push_cast; ring
    rw [e]
    exact h3
  · obtain ⟨-, e, ⟨⟨es, hes, -⟩, -⟩, -⟩ := h.thP.vP i t
    have key := fun P (hP : P.under (𝓞 D.host.F) = v) =>
      (GlobalTheory.levCh_unramified_places D T0 R.toLevCh A.μ0 hL t).2.2.2 P fun PP hPP => by
        rw [hP]
        exact under_ne (hes PP (Finset.mem_union.2 hPP)) hv
    have u1 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.mu0 i) v ε hv.1 fun P hP => (key P hP).2 i
    have u2 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.xi t) v ε hv.1 fun P hP => (key P hP).1
    have u3 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hL.eta v ε hv.1 fun P _ => R.C.isEta.unr P
    have u4 : GlobalTheory.WeilParts.UnramAt ε (R.toLevCh.mu t ((i : ℕ) + 1)) := fun x a b c => by
      show R.mu0 ((i : ℕ) + 1) x * R.xi t x = 1
      rw [u1 x a b c, u2 x a b c, one_mul]
    refine ⟨u4, fun x a b c => ?_⟩
    show R.toLevCh.mu t ((i : ℕ) + 1) x * (R.eta x)⁻¹ = 1
    rw [u4 x a b c, u3 x a b c, inv_one, one_mul]
  · rw [rV]
    exact (Nat.add_pos_left hr.pos _).ne'
  · rw [lV, ← GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, hV.2]
    rfl

end GlobalTheory.AdTh.RecPairCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.VBExt

section Algebra

variable {R A B C : Type} [CommRing R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
  {ι κ : Type} [Fintype ι] [Fintype κ]

theorem bijective_sumElim (hfg : Function.Exact f g) (hf : Function.Injective f)
    (a : Module.Basis ι R A) (c : Module.Basis κ R C) (t : κ → B) (ht : ∀ k, g (t k) = c k) :
    Function.Bijective (Fintype.linearCombination R (Sum.elim (fun i => f (a i)) t)) := by
  have hg (x : ι ⊕ κ → R) : g (Fintype.linearCombination R (Sum.elim (fun i => f (a i)) t) x) =
      ∑ k, x (.inr k) • c k := by
    simp [Fintype.linearCombination_apply, Fintype.sum_sum_type, hfg.apply_apply_eq_zero, ht]
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have h2 : ∀ k, x (.inr k) = 0 :=
      Fintype.linearIndependent_iff.1 c.linearIndependent _ (by rw [← hg, hx, map_zero])
    have h1 : ∀ i, x (.inl i) = 0 :=
      Fintype.linearIndependent_iff.1 a.linearIndependent _ (hf (by
        simpa [Fintype.linearCombination_apply, Fintype.sum_sum_type, h2] using hx))
    funext j
    rcases j with i | k
    exacts [h1 i, h2 k]
  · intro y
    obtain ⟨z, hz⟩ := (hfg (y - ∑ k, c.repr (g y) k • t k)).1 (by
      simp [ht])
    refine ⟨Sum.elim (a.repr z) (c.repr (g y)), ?_⟩
    have : ∑ i, a.repr z i • f (a i) = f z := by
      conv_rhs => rw [← a.sum_repr z]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
    simp [Fintype.linearCombination_apply, Fintype.sum_sum_type, this, hz]

theorem det_sumElim [DecidableEq ι] [DecidableEq κ] (hfg : ∀ x, g (f x) = 0)
    (a : Module.Basis ι R A) (c : Module.Basis κ R C) (b : Module.Basis (ι ⊕ κ) R B)
    (hb : ∀ i, b (.inl i) = f (a i)) (hc : ∀ k, g (b (.inr k)) = c k) (a' : ι → A) (t' : κ → B) :
    b.det (Sum.elim (fun i => f (a' i)) t') = a.det a' * c.det fun k => g (t' k) := by
  have h1 (x : A) : ⇑(b.repr (f x)) = Sum.elim (a.repr x) 0 := by
    have : f x = ∑ j, Sum.elim (a.repr x) 0 j • b j := by
      conv_lhs => rw [← a.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Fintype.sum_sum_type, hb, map_sum, map_smul, Sum.elim_inl, Sum.elim_inr,
        Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    rw [this, b.repr_sum_self]
  have h2 (y : B) (k : κ) : b.repr y (.inr k) = c.repr (g y) k := by
    have : g y = ∑ k, b.repr y (.inr k) • c k := by
      conv_lhs => rw [← b.sum_repr y]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Fintype.sum_sum_type, hb, hc, hfg, map_sum, map_smul, map_add (f := _), smul_zero,
        Finset.sum_const_zero, zero_add]
    rw [this, c.repr_sum_self]
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply,
    ← Matrix.det_fromBlocks_zero₂₁ _ (Matrix.of fun i k => b.repr (t' k) (.inl i))]
  congr 1
  ext (i | i) (j | j) <;> simp [Module.Basis.toMatrix_apply, h1, h2, hfg]

end Algebra

variable {X : Scheme.{0}} {S : ShortComplex X.Modules} {U U' V : X.Opens} {r s : ℕ}

theorem isFrame_sumElim (hS : S.ShortExact) {ι κ : Type} [Fintype ι] [Fintype κ]
    {e : ι → Γ(S.X₁, U)} {t : κ → Γ(S.X₂, U)} (he : IsFrame e)
    (ht : IsFrame fun k => S.g.app U (t k)) :
    IsFrame (Sum.elim (fun i => S.f.app U (e i)) t) := fun V h => by
  have := hS.mono_f
  have key := bijective_sumElim (f := appLinear S.f V) (g := appLinear S.g V)
    (QCoh.exact_app_of_exact_of_mono hS.exact V) (QCoh.injective_app_of_mono S.f V)
    (he.basis h) (ht.basis h) (fun k => resM _ h (t k))
    (fun k => by rw [IsFrame.basis_apply, appLinear_apply, app_resM])
  convert key using 3
  funext j
  rcases j with i | k
  · simp only [Sum.elim_inl, IsFrame.basis_apply, appLinear_apply, app_resM]
  · rfl

theorem detUnit_sumElim (hS : S.ShortExact) {e : Fin r → Γ(S.X₁, U)} {t : Fin s → Γ(S.X₂, U)}
    (he : IsFrame e) (ht : IsFrame fun k => S.g.app U (t k)) {e' : Fin r → Γ(S.X₁, U')}
    {t' : Fin s → Γ(S.X₂, U')} (he' : IsFrame e') (ht' : IsFrame fun k => S.g.app U' (t' k))
    (h : V ≤ U) (h' : V ≤ U') :
    ((isFrame_sumElim hS he ht).comp_equiv finSumFinEquiv.symm).detUnit
      ((isFrame_sumElim hS he' ht').comp_equiv finSumFinEquiv.symm) h h' =
      he.detUnit he' h h' * ht.detUnit ht' h h' := by
  have := hS.mono_f
  refine Units.ext ?_
  have e₁ : ((isFrame_sumElim hS he ht).comp_equiv finSumFinEquiv.symm).basis h =
      ((isFrame_sumElim hS he ht).basis h).reindex finSumFinEquiv :=
    DFunLike.ext _ _ fun k => by simp
  have key := det_sumElim (f := appLinear S.f V) (g := appLinear S.g V)
    (QCoh.exact_app_of_exact_of_mono hS.exact V).apply_apply_eq_zero
    (he.basis h) (ht.basis h) ((isFrame_sumElim hS he ht).basis h)
    (fun i => by simp only [Sum.elim_inl, IsFrame.basis_apply, appLinear_apply, app_resM])
    (fun i => by simp only [Sum.elim_inr, IsFrame.basis_apply, appLinear_apply, app_resM])
    (fun i => resM _ h' (e' i)) (fun k => resM _ h' (t' k))
  simp only [appLinear_apply, app_resM] at key
  rw [Units.val_mul, IsFrame.val_detUnit, IsFrame.val_detUnit, IsFrame.val_detUnit, e₁,
    Module.Basis.det_reindex, ← key]
  congr 1
  funext j
  rcases j with i | k <;> simp

theorem exists_lifts {F G : X.Modules} (φ : F ⟶ G) [Epi φ] {κ : Type} [Fintype κ]
    (c : κ → Γ(G, U)) {x : X} (hx : x ∈ U) :
    ∃ (W : X.Opens) (h : W ≤ U), x ∈ W ∧ ∃ t : κ → Γ(F, W), ∀ k, φ.app W (t k) = resM G h (c k) := by
  choose W hW hxW t ht using fun k => exists_app_eq_of_epi φ (c k) hx
  have hV (k : κ) : U ⊓ Finset.univ.inf W ≤ W k :=
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ k))
  refine ⟨U ⊓ Finset.univ.inf W, inf_le_left, ⟨hx, by
    rw [Opens.coe_finset_inf]; simpa using hxW⟩, fun k => resM F (hV k) (t k), fun k => ?_⟩
  rw [app_resM, ht, resM_resM]


variable (S r s) in
structure AdaptedChart where

  U : X.Opens

  e : Fin r → Γ(S.X₁, U)

  t : Fin s → Γ(S.X₂, U)

  he : IsFrame e

  ht : IsFrame fun k => S.g.app U (t k)

theorem exists_adaptedChart (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (x : X) :
    ∃ c : AdaptedChart S r s, x ∈ c.U := by
  have := hS.epi_g
  obtain ⟨U, e, hx, he⟩ := h₁ x
  obtain ⟨U', c, -, hx', hle, hc⟩ := h₃.exists_affine hx
  obtain ⟨W, h, hxW, t, ht⟩ := exists_lifts S.g c hx'
  exact ⟨⟨W, _, t, he.res (h.trans hle), by rw [funext ht]; exact hc.res h⟩, hxW⟩

theorem isVB_and_cls_det_of_shortExact (X : Scheme.{0}) (S : ShortComplex X.Modules) (r s : ℕ)
    (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) :
    ∃ h₂ : IsVB S.X₂ (r + s),
      CechPic.cls _ h₂.isLB_det = CechPic.cls _ h₁.isLB_det + CechPic.cls _ h₃.isLB_det := by
  have hb (c : AdaptedChart S r s) := (isFrame_sumElim hS c.he c.ht).comp_equiv finSumFinEquiv.symm
  let L : LB X :=
    { ι := AdaptedChart S r s
      U := fun c => c.U
      g := fun c c' => (hb c).detUnit (hb c') inf_le_left inf_le_right }
  have hL : L.IsLB := by
    refine ⟨top_le_iff.1 fun x _ => ?_, fun c => ?_, fun c c' c'' => ?_⟩
    · exact Opens.mem_iSup.2 (exists_adaptedChart hS h₁ h₃ x)
    · exact (IsFrame.res_detUnit _ _ _ _ _).trans ((hb c).detUnit_self _ _)
    · exact (congrArg₂ (· * ·) (IsFrame.res_detUnit _ _ _ _ _)
        (IsFrame.res_detUnit _ _ _ _ _)).trans
        ((IsFrame.detUnit_mul _ _ _ _ _ _).trans (IsFrame.res_detUnit _ _ _ _ _).symm)
  obtain ⟨h₂, hi⟩ := lbIso_det_of_frames hL _ hb fun _ _ => rfl
  have hT := CechPic.isLB_tens h₁.isLB_det h₃.isLB_det
  have hj : LBIso L (CechPic.tens (det S.X₁ r) (det S.X₃ s)) := CechPic.iso_of_chart hT
    ⟨fun c => (⟨c.U, c.e, c.he⟩, ⟨c.U, _, c.ht⟩), fun _ _ h => ⟨h, h⟩, fun y c c' hc hc' =>
      ((congrArg _ (detUnit_sumElim hS c.he c.ht c'.he c'.ht _ _)).trans (map_mul _ _ _)).trans
        (CechPic.gm_tens (det S.X₁ r) (det S.X₃ s) (𝟙 X) y (⟨c.U, c.e, c.he⟩, ⟨c.U, _, c.ht⟩)
          (⟨c'.U, c'.e, c'.he⟩, ⟨c'.U, _, c'.ht⟩) ⟨hc, hc⟩ ⟨hc', hc'⟩).symm⟩
  exact ⟨h₂, ((CechPic.cls_eq_iff hL _).2 hi).symm.trans ((CechPic.cls_eq_iff hL hT).2 hj)⟩

end GlobalTheory.VBExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JKInvOfTriv
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial

namespace GlobalTheory.ExpFrame.HeckeMod

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)
  (jK : F.K →* alg F.O N lam) (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
  [IsScalarTower F.O (alg F.O N lam) W]

theorem mem_forms {f : F.G → W} : f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W ↔
    ∀ (γ : F.Γ) (g : F.G) (κ : F.K), f ((γ : F.G) * g * κ) = jK κ⁻¹ • f g := Iff.rfl


variable {F lam jK} in
theorem jK_eq (hJ : F.IsJ lam jK) {κ κ' : F.K} (h1 : F.kap κ' = F.kap κ) (h2 : F.chi κ' = F.chi κ) : jK κ' = jK κ := by
  rw [hJ κ', hJ κ, h1, h2]

variable {F lam jK} in
theorem jK_inv_congr {κ κ' : F.K} (h : jK κ' = jK κ) : jK κ'⁻¹ = jK κ⁻¹ := by
  have e1 : jK κ'⁻¹ * jK κ' = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have e2 : jK κ * jK κ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc jK κ'⁻¹ = jK κ'⁻¹ * (jK κ * jK κ⁻¹) := by rw [e2, mul_one]
    _ = (jK κ'⁻¹ * jK κ') * jK κ⁻¹ := by rw [h, mul_assoc]
    _ = jK κ⁻¹ := by rw [e1, one_mul]

theorem grpA_one : grpA F.O N lam 1 = 1 := Subtype.ext (by simp [grpA, grp])


variable {F lam jK} in
theorem jK_inv_of_triv (hJ : F.IsJ lam jK) {κ : F.K} (h1 : F.kap κ = 1) (h2 : F.chi κ = 1) : jK κ⁻¹ = 1 := by
  have : jK κ = jK 1 := by rw [hJ κ, h1, h2, map_one, grpA_one]; simp
  rw [jK_inv_congr this, inv_one, map_one]

def heckeFn (i : F.I) (f : F.G → W) : F.G → W := fun g => F.cst i • ∑ s ∈ F.tr i, f (g * s)

variable {F lam jK W}

theorem heckeFn_mem (hOk : F.Ok) (hJ : F.IsJ lam jK) (i : F.I) {f : F.G → W}
    (hf : f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W) : heckeFn F W i f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W := by
  rw [mem_forms] at hf ⊢
  intro γ g κ
  obtain ⟨σ, hσ⟩ := hOk.perm i κ
  have key : ∀ s : F.tr i, f ((γ : F.G) * g * κ * s) = jK κ⁻¹ • f (g * (σ s : F.G)) := by
    intro s
    obtain ⟨κ', h1, h2, h3⟩ := hσ s
    have e : (γ : F.G) * g * κ * s = γ * (g * σ s) * κ' := by
      rw [mul_assoc ((γ : F.G) * g) (κ : F.G) (s : F.G), h1]; simp only [mul_assoc]
    rw [e, hf γ (g * σ s) κ', jK_inv_congr (jK_eq hJ h2 h3)]
  simp only [heckeFn]
  rw [← Finset.sum_coe_sort (F.tr i), ← Finset.sum_coe_sort (F.tr i)]
  simp_rw [key]
  rw [← Finset.smul_sum, Equiv.sum_comp σ (fun s : F.tr i => f (g * (s : F.G))), smul_comm]

theorem heckeFn_comm (hOk : F.Ok) (hJ : F.IsJ lam jK) (i j : F.I) {f : F.G → W}
    (hf : f ∈ Forms F.O (A := alg F.O N lam) F.Γ jK W) :
    heckeFn F W i (heckeFn F W j f) = heckeFn F W j (heckeFn F W i f) := by
  rw [mem_forms] at hf
  funext g
  obtain ⟨σ, hσ⟩ := hOk.comm i j
  have key : ∀ x : F.tr i × F.tr j, f (g * x.1 * x.2) = f (g * (σ x).1 * (σ x).2) := by
    intro x
    obtain ⟨hK, h1, h2⟩ := hσ x
    have e : g * x.1 * x.2 = ((1 : F.Γ) : F.G) * (g * (σ x).1 * (σ x).2) * (⟨_, hK⟩ : F.K) := by
      simp only [OneMemClass.coe_one, one_mul, mul_assoc, mul_inv_cancel_left]
    rw [e, hf, jK_inv_of_triv hJ h1 h2, one_smul]
  have hsum : ∀ (a b : F.I), heckeFn F W a (heckeFn F W b f) g =
      F.cst a • F.cst b • ∑ x : F.tr a × F.tr b, f (g * x.1 * x.2) := by
    intro a b
    simp only [heckeFn, Fintype.sum_prod_type, Finset.smul_sum]
    rw [← Finset.sum_coe_sort (F.tr a)]
    refine Fintype.sum_congr _ _ fun s => ?_
    rw [← Finset.sum_coe_sort (F.tr b)]
  rw [hsum, hsum, smul_comm (F.cst i) (F.cst j)]
  congr 2
  rw [Fintype.sum_congr _ _ key, Equiv.sum_comp σ (fun y : F.tr j × F.tr i => f (g * y.1 * y.2))]

end GlobalTheory.ExpFrame.HeckeMod

namespace GlobalTheory.ExpFrame.HeckeMod

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
  {jK : F.K →* alg F.O N lam} {W : Type} [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
  [IsScalarTower F.O (alg F.O N lam) W]

def op (hOk : F.Ok) (hJ : F.IsJ lam jK) (i : F.I) :
    Module.End F.O (Forms F.O (A := alg F.O N lam) F.Γ jK W) where
  toFun f := ⟨heckeFn F W i f, heckeFn_mem hOk hJ i f.2⟩
  map_add' f f' := by
    ext g
    simp [heckeFn, Finset.sum_add_distrib, smul_add]
  map_smul' c f := by
    ext g
    simp [heckeFn, Finset.smul_sum, smul_comm (F.cst i) c]

theorem op_comm (hOk : F.Ok) (hJ : F.IsJ lam jK) (i j : F.I) :
    (op (W := W) hOk hJ i) * op hOk hJ j = op hOk hJ j * op hOk hJ i := by
  ext f : 1
  exact Subtype.ext (heckeFn_comm hOk hJ i j f.2)

end GlobalTheory.ExpFrame.HeckeMod

namespace GlobalTheory.ExpFrame.HeckeMod

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
  {jK : F.K →* alg F.O N lam} {W : Type} [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W]
  [IsScalarTower F.O (alg F.O N lam) W]

open scoped IsMulCommutative in
def heckeAlg (hOk : F.Ok) (hJ : F.IsJ lam jK) : F.T →ₐ[F.O] Module.End F.O (Forms F.O (A := alg F.O N lam) F.Γ jK W) :=
  letI : IsMulCommutative (Algebra.adjoin F.O (Set.range (op (W := W) hOk hJ))) :=
    Algebra.isMulCommutative_adjoin F.O (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact op_comm hOk hJ i j)
  (Algebra.adjoin F.O (Set.range (op (W := W) hOk hJ))).val.comp
    (MvPolynomial.aeval fun i => ⟨op hOk hJ i, Algebra.subset_adjoin ⟨i, rfl⟩⟩)

theorem heckeAlg_X (hOk : F.Ok) (hJ : F.IsJ lam jK) (i : F.I) : heckeAlg (W := W) hOk hJ (X i) = op hOk hJ i := by
  simp [heckeAlg]

theorem hecke_module : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam), F.Ok → F.IsJ lam jK → ∀ (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W] [IsScalarTower F.O (alg F.O N lam) W], ∃ (_ : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)) (_ : IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)), F.IsHecke lam jK W := by
  intro l _ ι _ _ N F lam jK hOk hJ W _ _ _ _
  letI inst : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W) := Module.compHom _ (heckeAlg (W := W) hOk hJ).toRingHom
  refine ⟨inst, ⟨fun c t f => ?_⟩, fun c f => ?_, fun i f g => ?_⟩
  · change heckeAlg hOk hJ (c • t) f = c • heckeAlg hOk hJ t f
    rw [map_smul, LinearMap.smul_apply]
  · change heckeAlg hOk hJ (C c) f = c • f
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply]
  · change ((heckeAlg hOk hJ (X i) f : Forms F.O (A := alg F.O N lam) F.Γ jK W) : F.G → W) g = _
    rw [heckeAlg_X]
    rfl

end GlobalTheory.ExpFrame.HeckeMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelFiniteQuasicoherent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.LatFinite

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]
  {M : X → AddSubgroup V} {F : X.Modules}

theorem val_linearCombination (L : LatModel M F) {U W : X.Opens} (h : W ≤ U)
    (hW : genericPoint X ∈ W) {m : ℕ} (e : Fin m → Γ(F, U)) (a : Fin m → Γ(X, W)) :
    L.val W hW (Fintype.linearCombination Γ(X, W) (fun i => Twist.resM F h (e i)) a) =
      ∑ i, fnOf W hW (a i) • L.val U (h hW) (e i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Fintype.linearCombination_apply, map_sum, L.smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← L.res U W h hW (e i)]

theorem val_mem (L : LatModel M F) {W : X.Opens} (hW : genericPoint X ∈ W) (s : Γ(F, W))
    {z : X} (hz : z ∈ W) : L.val W hW s ∈ M z := by
  have h : L.val W hW s ∈ latSec M W := L.range W hW ▸ ⟨s, rfl⟩
  simp only [latSec, AddSubgroup.mem_iInf] at h
  exact h z hz

theorem isFrame (L : LatModel M F) {U : X.Opens} (hU : genericPoint X ∈ U) {m : ℕ}
    {v : Fin m → V} (hv : LinearIndependent X.functionField v)
    (hM : ∀ z ∈ U, ∀ w, w ∈ M z ↔
      ∃ c : Fin m → X.functionField, (∀ i, RegAt z (c i)) ∧ w = ∑ i, c i • v i)
    (e : Fin m → Γ(F, U)) (he : ∀ i, L.val U hU (e i) = v i) : VB.IsFrame e := by
  refine VB.isFrame_of_forall_exists fun W h x hx => ⟨W, le_rfl, hx, ?_⟩
  have hW : genericPoint X ∈ W := gen_mem hx
  have key : ∀ a : Fin m → Γ(X, W), L.val W hW (Fintype.linearCombination Γ(X, W)
      (fun i => Twist.resM F (le_rfl.trans h) (e i)) a) = ∑ i, fnOf W hW (a i) • v i := fun a => by
    rw [val_linearCombination L]
    simp only [he]
  constructor
  · intro a b hab
    have := congrArg (L.val W hW) hab
    rw [key, key] at this
    funext i
    exact fnOf_injective W hW (Fintype.linearIndependent_iffₛ.1 hv _ _ this i)
  · intro s
    obtain ⟨c, -, hc⟩ := (hM _ (h hW) _).1 (val_mem L hW s hW)
    have hreg : ∀ i, ∀ z ∈ W, RegAt z (c i) := by
      intro i z hz
      obtain ⟨c', hc', e'⟩ := (hM z (h hz) _).1 (val_mem L hW s hz)
      rw [Fintype.linearIndependent_iffₛ.1 hv _ _ (hc.symm.trans e') i]
      exact hc' i
    choose a ha using fun i => exists_fnOf_eq hW (hreg i)
    refine ⟨a, L.inj W hW ?_⟩
    rw [key, hc]
    simp only [ha]

theorem isFiniteQC_of_latModel : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V]
    [Module X.functionField V] (M : X → AddSubgroup V) (F : X.Modules), LatModel M F →
    (∀ y : X, ∃ (U : X.Opens) (m : ℕ) (v : Fin m → V), y ∈ U ∧ IsAffineOpen U ∧
      LinearIndependent X.functionField v ∧ ∀ z ∈ U, ∀ w, w ∈ M z ↔
        ∃ c : Fin m → X.functionField, (∀ i, RegAt z (c i)) ∧ w = ∑ i, c i • v i) →
    GlobalTheory.QCoh.IsFiniteQC F := by
  intro X _ V _ _ M F L H
  choose U m v hy _ hv hM using H
  have frame : ∀ y, ∃ e : Fin (m y) → Γ(F, U y), VB.IsFrame e := by
    intro y
    have hU : genericPoint X ∈ U y := gen_mem (hy y)
    have hmem : ∀ i, v y i ∈ latSec M (U y) := by
      intro i
      simp only [latSec, AddSubgroup.mem_iInf]
      intro z hz
      classical
      refine (hM y z hz _).2 ⟨Pi.single i 1, fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; simpa using (unitAt_one z).regAt
        · simpa [Pi.single_apply, hj] using regAt_zero z
      · simp [Pi.single_apply]
    choose e he using fun i => (L.range (U y) hU).ge (hmem i)
    exact ⟨e, isFrame L hU (hv y) (hM y) e he⟩
  choose e he using frame
  refine QCoh.IsFiniteQC.of_restrict (fun y => (U y).ι) (fun x => ⟨x, by simpa using hy x⟩)
    fun y => ?_
  have hf := (VB.isFrame_restrict_iff (U y).ι _).2 ((he y).res ((U y).ι_image_le ⊤))
  exact (VB.IsFrame.isVB hf).isFiniteQC

end GlobalTheory.LogDR.LatFinite
end
end

