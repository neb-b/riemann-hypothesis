module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideTwistedConsistent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0398
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEqOfAutomorphismMapsParahoric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterEqOfCommonUnipotentLevelEigenve
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0685
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0688
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClassTrivialStabiliserAtTypePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0686
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0681
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0680
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JointEtaOfAdmissibleTwist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0683

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevCmp

variable {D : D7}

theorem grpShape_of {η : HChar D.host.E} {J : Subgroup (GAf D.host.E D.R.nV)} {χ : J →* ℂˣ} (h1 : NG.IsProdLevel J)
    (h2 : ParaShape D η J χ)
    (h3 : ∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → ∃ ψ₀ ξ, NG.LevelUni J χ s D.R.r ψ₀ ξ)
    (h4 : NG.HypOutside J χ (gPl D ∪ qPl D η)) : GrpShape D η J :=
  ⟨h1, fun v hv => let ⟨s, _, a, _, c⟩ := h2 v hv; ⟨s, a, c.mem⟩, fun k v s hs => let ⟨_, _, c⟩ := h3 k v s hs; c.mem,
    fun κ hκ => (h4 κ hκ).1⟩

theorem exists_form {η : HChar D.host.E} {J : Subgroup (GAf D.host.E D.R.nV)} (hG : GPlaces D) (h : GrpShape D η J)
    (K : Type) [Field K] (W : Type) [AddCommGroup W] [Module K W] (ρ : Representation K (GQ D.host.E D.R.nV) W)
    (hρ : ρ.IsIrreducible) (χ : J →* Kˣ) : ∃ f ∈ NX.TypeSpF D.host.E D.R.nV K ρ J χ, f ≠ 0 := by
  obtain ⟨k, ⟨v⟩⟩ := hG.2.2
  obtain ⟨h1, s, hs⟩ := hG.1 k v
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.NeatUni.exists_trivial_stabiliser D k s (hs ▸ h1)
  haveI : Nontrivial W := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have := hρ
    have h2 : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
    exact h2 (Subrepresentation.ext (Subsingleton.elim _ _))
  exact _root_.GlobalTheory.ClassForm.exists_form_of_trivial_stabiliser _ _ K W ρ J χ g fun γ hγ hm =>
    hg γ hγ (_root_.GlobalTheory.LevShapeBound.bound D η J hG h _ hm).1 ((_root_.GlobalTheory.LevShapeBound.bound D η J hG h _ hm).2 k v s hs)

theorem para_rigid {L : Type} [Field L] [NumberField L] [IsCMField L] {n r : ℕ} {s : SplitPlace L} {V : Type} [AddCommGroup V]
    [Module ℂ V] {F : GAf L n → V} {J : Subgroup (GAf L n)} {χ χ' : J →* ℂˣ}
    {ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ} (hF : F ≠ 0) (h : NG.LevelPara J χ s r ξ)
    (hr : ∃ a : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v (a : s.v.adicCompletion (maximalRealSubfield L)) = 1 ∧ ξ a ≠ 1)
    (h1 : ∀ κ, χ' κ = 1 ↔ χ κ = 1) (hE : ∀ κ : J, Eig F κ (χ' κ : ℂˣ)) :
    ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → (∃ c, Eig F κ c) → NG.ParaRT s r (s.loc n κ) := by
  obtain ⟨a, ha, ha'⟩ := hr
  refine _root_.GlobalTheory.ParaRigid.mem_para_of_eig L n r s V F J χ' a hF ha h.mem hE (fun κ hκ ht hd => (h1 _).2 ?_) fun κ hκ ht hd e => ha' ?_
  · rw [h.chr κ hκ ht 1 hd.symm, map_one]
  · rw [← h.chr κ hκ ht a hd.symm]
    exact (h1 _).1 e

theorem cx_eq_one {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] (e : K →+* ℂ)
    {J : Subgroup (GAf L n)} (χ : J →* Kˣ) (κ : J) : cx e χ κ = 1 ↔ χ κ = 1 := by
  rw [← Units.val_inj, cx_apply, Units.val_one, map_eq_one_iff e e.injective, Units.val_eq_one]

theorem levEq {η : HChar D.host.E} {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m)
    (e : NX.Kk D i k →+* ℂ) (he : SideRead i b k e) (hG : GPlaces D)
    (hram : ∀ (s : SplitPlace D.host.E) ξ, s.v ∈ qPl D η → NG.IsCompAt η s ξ →
      ∃ a : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
        Valued.v (a : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 ∧ ξ a ≠ 1)
    (m1 : NG.IsProdLevel m.J) (m2 : ParaShape D η m.J m.χ)
    (m3 : ∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v → ∃ ψ₀ ξ, NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt η s ξ ∧
      NG.LevelUni m.J m.χ s D.R.r ψ₀ ξ)
    (m4 : NG.HypOutside m.J m.χ (gPl D ∪ qPl D η)) (x0 : NX.badV D i Q ⊆ gPl D ∪ qPl D η)
    (x2 : ParaShape D η (cell X b hA j).J (cx e (cell X b hA j).χ))
    (x3 : ∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v → ∃ ψ₀ ξ, NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt η s ξ ∧
      ∀ e, SideRead i b k e → NG.LevelUni (cell X b hA j).J (cx e (cell X b hA j).χ) s D.R.r ψ₀ ξ)
    (hJ : Joint η m X b hA j) : LevEq m.J m.χ (cell X b hA j).J (cx e (cell X b hA j).χ) := by
  have x1 := _root_.GlobalTheory.LevProd.main D X i b k Q ψ hA j
  have x4 : NG.HypOutside (cell X b hA j).J (cx e (cell X b hA j).χ) (gPl D ∪ qPl D η) := fun κ hκ => by
    have h := (cell X b hA j).hyp κ fun v hv => hκ v fun h => hv fun h' => h (x0 h')
    exact ⟨h.1, fun h' => (cx_eq_one _ _ _).2 (h.2 h')⟩
  have gm := grpShape_of m1 m2 (fun k v s hs => let ⟨a, c, _, _, d⟩ := m3 k v s hs; ⟨a, c, d⟩) m4
  have gx := grpShape_of x1 x2 (fun k v s hs => let ⟨a, c, _, _, d⟩ := x3 k v s hs; ⟨a, c, d e he⟩) x4
  obtain ⟨θ, J₁, e', V, _, _, ω, hθ, he', hω, j1, j2, j3⟩ := hJ
  obtain ⟨f, hf, hf0⟩ := exists_form hG gm ℂ _ m.wt.ρ m.wt.irr m.χ
  obtain ⟨f', hf', hf0'⟩ := exists_form hG gx _ _ (cell X b hA j).ρ (cell X b hA j).irr (cell X b hA j).χ
  obtain ⟨y, rfl⟩ : f ∈ LinearMap.range m.real := by
    rw [m.real_range]
    obtain ⟨N, hN, h⟩ := m.J_open
    refine ⟨⟨hf.1, N, hN, fun κ hκ g => ?_⟩, fun κ => funext fun g => hf.2 κ g⟩
    obtain ⟨h1, h2⟩ := h κ hκ
    have := hf.2 ⟨κ, h1⟩ g
    rwa [h2, Units.val_one, one_smul] at this
  obtain ⟨y', hy'⟩ := (cell X b hA j).real.surjective ⟨f', hf'⟩
  set F' : GAf D.host.E D.R.nV → V := fun g => ω (((cell X b hA j).real y').1 g) with hF'
  have hF0 : F' ≠ 0 := fun h => hf0' (funext fun g => hω (by
    have := congrFun h g
    rw [hF'] at this
    simp only [hy'] at this
    exact this.trans (map_zero ω).symm))
  have E1 : ∀ κ : m.J, Eig (m.real y) κ (m.χ κ : ℂˣ) := fun κ g => hf.2 κ g
  have E2 : ∀ κ : (cell X b hA j).J, Eig F' κ (cx e' (cell X b hA j).χ κ : ℂˣ) := fun κ g => by
    have := ((cell X b hA j).real y').2.2 κ g
    simp only [hF', this, map_smulₛₗ, cx_apply]
  have hr0 : 2 ≤ D.R.r := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; unfold Ranks.r; omega
  have hr1 : D.R.r < D.R.nV := by have := D.R.rank_add_five_le; unfold Ranks.nV; omega
  refine _root_.GlobalTheory.LevCmp.levEq_of_agree _ _ _ _ _ _ _ (_root_.GlobalTheory.LevCmp.gPl_union_qPl_finite D η) m1 x1 m4 x4 fun u hu => ?_
  rcases hu with hu | hu
  · obtain ⟨kk, v, s, rfl, hs⟩ := hG.2.1 u hu
    obtain ⟨p, ξ, a1, a2, a3⟩ := m3 kk v s hs
    obtain ⟨p', ξ', b1, b2, b3⟩ := x3 kk v s hs
    obtain rfl := _root_.GlobalTheory.CompAtUniq.main _ η s ξ ξ' a2 b2
    have hg := D.host.g_prime kk
    have hab : s.Above (D.host.g kk) := by
      have h1 : ((D.host.g kk : ℕ) : 𝓞 D.host.E) ∈ s.w.asIdeal := hs ▸ (hG.1 kk v).1
      show _ ∈ s.v.asIdeal
      rw [← s.w_under]
      show algebraMap _ (𝓞 D.host.E) _ ∈ s.w.asIdeal
      rwa [map_natCast]
    have key := _root_.GlobalTheory.PsiCmp.fractionFieldToGenericStalk_algebraMap_eq _ _ _ s (D.host.g kk) (D.host.g kk - 1) θ _ _ (m.real y) F' _ _ _ _ p p' ξ ξ hg hab
      ((Nat.coprime_self_sub_left hg.one_le).2 (Nat.coprime_one_left _)) hr0 hr1.le hθ hf0 hF0 a1 b1 a3 (b3 e' he') E1 E2
      fun κ hκ hU => let ⟨c, c', h1, h2, h3⟩ := j3 κ (j2 kk v s hs κ hκ hU); ⟨c, c', h1 y, h2 y', h3 kk v s hs hκ⟩
    refine fun κ hκ => ⟨(a3.mem κ hκ).trans ((b3 e he).mem κ hκ).symm, fun h h' => ?_⟩
    obtain ⟨u1, u2⟩ := _root_.GlobalTheory.ParaUnit.detDD_unit_supDiag_int _ _ _ s _ ((a3.mem κ hκ).1 h).1
    have hne : NG.detDD s D.R.r (s.loc _ κ) ≠ 0 := fun h0 => by simp [h0] at u1
    apply Units.ext
    rw [a3.chr κ h hκ (Units.mk0 _ hne) rfl, (b3 e he).chr κ h' hκ (Units.mk0 _ hne) rfl, key _ u2]
  · obtain ⟨s, ξ, rfl, a2, a3⟩ := m2 u hu
    obtain ⟨s', ξ', b1, b2, b3⟩ := x2 _ hu
    obtain ⟨s₁, c1, c2⟩ := j1 _ hu
    have hU : ∀ κ, TrivOutside {s.v} κ → NG.ParaRT s₁ D.R.r (s₁.loc _ κ) → κ ∈ Umax D.host.E D.R.nV := fun κ hκ hP =>
      (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s₁ (c1 ▸ hκ)).1 hP.1
    have hs : s' = s := _root_.GlobalTheory.ParaOpp.splitPlace_eq_of_para _ _ _ s s' s₁ θ (by omega) hr1 b1 c1 hθ fun κ hκ hP => by
      obtain ⟨c, c', h1, h2, -⟩ := j3 κ (c2 κ (c1 ▸ hκ) hP)
      have h3 := (hθ.1 κ).2 (hU κ hκ hP)
      have h4 := (hθ.2 _ κ).2 hκ
      exact ⟨para_rigid hf0 a3 (hram s ξ hu a2) (fun _ => Iff.rfl) E1 _ h3 h4 ⟨c, h1 y⟩,
        para_rigid hF0 b3 (hram s' ξ' (b1 ▸ hu) b2) (fun κ => (cx_eq_one _ _ _).trans (cx_eq_one _ _ _).symm) E2 _ h3
          (b1 ▸ h4) ⟨c', h2 y'⟩⟩
    subst hs
    obtain rfl := _root_.GlobalTheory.CompAtUniq.main _ η s' ξ ξ' a2 b2
    refine fun κ hκ => ⟨(a3.mem κ hκ).trans (b3.mem κ hκ).symm, fun h h' => ?_⟩
    obtain ⟨u1, -⟩ := _root_.GlobalTheory.ParaUnit.detDD_unit_supDiag_int _ _ _ s' _ ((a3.mem κ hκ).1 h)
    have hne : NG.detDD s' D.R.r (s'.loc _ κ) ≠ 0 := fun h0 => by simp [h0] at u1
    rw [a3.chr κ h hκ (Units.mk0 _ hne) rfl, b3.chr κ h' hκ (Units.mk0 _ hne) rfl]

theorem unpack {p : TwPack D} {b : Bool} {w : D.what₂.places.Pl} {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : GlobalTheory.TwistChoice.HasReading p b w ψ₀) {i : D.ntw.Tw} {Q : Finset (PlE D.host)} {k : ℕ} (h1 : p.1 = i) (h2 : p.2.1 = Q)
    (h3 : p.2.2.1 = k) : ∃ (ρ : Reading i k b w) (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ), ρ.Pulls ψ ψ₀ ∧ twPack D i b Q k ψ = p := by
  obtain ⟨i', Q', k', φ⟩ := p
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨ρ, _, hρ, congrArg (fun ψ => (⟨i', Q', k', ψ⟩ : TwPack D)) (psiAt_psiAt b φ)⟩

theorem pack_pow {i i' : D.ntw.Tw} {k k' : ℕ} {b b' : Bool} {v v' : D.what₂.places.Pl} (ρ : Reading i k b v) (ρ' : Reading i' k' b' v')
    {Q Q' : Finset (PlE D.host)} {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} {ψ' : D.ntw.RCG i' Q' →* (D.ntw.Ok i' k')ˣ}
    {ψ₀ ψ₀' : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ} (h1 : i' = i) (h2 : Q' = Q) (h3 : k' = k) (h4 : ψ₀' = ψ₀)
    (hz : ∃ z : D.what₂.LL, IsPrimitiveRoot z (D.ntw.l i ^ k)) (ho : ∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) (hp : ρ.Pulls ψ ψ₀)
    (hp' : ρ'.Pulls ψ' ψ₀') :
    ∃ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) ∧ twPack D i' b' Q' k' ψ' = GlobalTheory.HeightCounting.twPackPow D a (twPack D i b Q k ψ) := by
  subst h1 h2 h3 h4
  obtain ⟨a, ha, rfl⟩ := _root_.GlobalTheory.LevCmp.pulls_eq_zpow D _ _ b b' v v' ρ ρ' _ ψ ψ' _ hz ho hp hp'
  refine ⟨if b = b' then a else -a, by split_ifs <;> simpa using ha, ?_⟩
  refine congrArg (fun ψ => (⟨i', Q', k', ψ⟩ : TwPack D)) ?_
  cases b <;> cases b'
  · exact (inv_zpow ψ a).symm
  · exact ((inv_zpow' ψ (-a)).trans (congrArg (ψ ^ ·) (neg_neg a))).symm
  · exact (zpow_neg ψ a).symm
  · rfl

theorem exists_data (hG : IsGalois ℚ ↥D.LL0) (s : D.what₂.places.Pl → D.ntw.Tw) (Q : D.what₂.places.Pl → Finset (PlE D.host))
    (k : D.what₂.places.Pl → ℕ) (ψ₀ : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ))
    (hs : ∀ v, ∃ b, ReadsAt (s v) b v) (c1 : ∀ v, s (D.what₂.places.conj v) = s v) (c2 : ∀ v, Q (D.what₂.places.conj v) = Q v)
    (c3 : ∀ v, k (D.what₂.places.conj v) = k v) (c4 : ∀ v, ψ₀ (D.what₂.places.conj v) = ψ₀ v)
    (hex : ∀ v b (ρ : Reading (s v) (k v) b v), ∃ ψ : D.ntw.RCG (s v) (Q v) →* (D.ntw.Ok (s v) (k v))ˣ, ρ.Pulls ψ (ψ₀ v)) :
    ∃ (b : D.what₂.places.Pl → Bool) (ρ : ∀ v, Reading (s v) (k v) (b v) v)
      (ψ : ∀ v, D.ntw.RCG (s v) (Q v) →* (D.ntw.Ok (s v) (k v))ˣ), (∀ v, ReadsAt (s v) (b v) v) ∧ (∀ v, (ρ v).Pulls (ψ v) (ψ₀ v)) ∧
      (∀ v, D.what₂.places.conj v ≠ v → b (D.what₂.places.conj v) = !b v) ∧
      ∀ v, twPack D (s (D.what₂.places.conj v)) (b (D.what₂.places.conj v)) (Q (D.what₂.places.conj v)) (k (D.what₂.places.conj v))
        (ψ (D.what₂.places.conj v)) = twPack D (s v) (b v) (Q v) (k v) (ψ v) := by
  classical
  choose b₀ hb using hs
  have h0 : ∀ v, ∃ p : TwPack D, GlobalTheory.TwistChoice.HasReading p (b₀ v) v (ψ₀ v) ∧ p.1 = s v ∧ p.2.1 = Q v ∧ p.2.2.1 = k v := fun v => by
    obtain ⟨ρ⟩ := (hb v).nonempty_reading (k v)
    obtain ⟨ψ, hψ⟩ := hex v _ ρ
    refine ⟨twPack D (s v) (b₀ v) (Q v) (k v) ψ, ⟨ρ, ?_⟩, rfl, rfl, rfl⟩
    show ρ.Pulls (BlochKatoReduction.Gen.psiAt (b₀ v) (BlochKatoReduction.Gen.psiAt (b₀ v) ψ)) _
    rwa [psiAt_psiAt]
  choose p hp using h0
  obtain ⟨o, ho⟩ := GlobalTheory.TwistChoice.exists_orbitRep (D := D)
  let b : D.what₂.places.Pl → Bool := fun w => if o w = w then b₀ w else !b₀ (D.what₂.places.conj w)
  have h1 : ∀ v, ReadsAt (s v) (b v) v ∧ ∃ (ρ : Reading (s v) (k v) (b v) v)
      (ψ : D.ntw.RCG (s v) (Q v) →* (D.ntw.Ok (s v) (k v))ˣ), ρ.Pulls ψ (ψ₀ v) ∧ twPack D (s v) (b v) (Q v) (k v) ψ = p (o v) := fun v => by
    by_cases h2 : o v = v
    · have e : b v = b₀ v := if_pos h2
      rw [e, h2]
      exact ⟨hb v, unpack (hp v).1 (hp v).2.1 (hp v).2.2.1 (hp v).2.2.2⟩
    · have e : b v = !b₀ (D.what₂.places.conj v) := if_neg h2
      have h3 := (hb (D.what₂.places.conj v)).conj hG
      have h4 := (hp (D.what₂.places.conj v)).1.conj hG
      rw [D.what₂.places.conj_conj] at h3 h4
      rw [c1] at h3
      rw [c4] at h4
      rw [e, (ho v).1.resolve_left h2]
      exact ⟨h3, unpack h4 ((hp _).2.1.trans (c1 v)) ((hp _).2.2.1.trans (c2 v)) ((hp _).2.2.2.trans (c3 v))⟩
  choose hr ρ ψ h2 h3 using h1
  refine ⟨b, ρ, ψ, hr, h2, fun w hne => ?_, fun v => by rw [h3, h3, (ho v).2]⟩
  simp only [b, (ho w).2, D.what₂.places.conj_conj]
  rcases (ho w).1 with h | h
  · rw [if_neg (by rw [h]; exact hne.symm), if_pos h]
  · rw [if_pos h, if_neg (by rw [h]; exact hne), Bool.not_not]

abbrev kMap {i : D.ntw.Tw} {k : ℕ} {b : Bool} {v : D.what₂.places.Pl} (ρ : Reading i k b v) : NX.Kk D i k →+* FractionRing ρ.Oe :=
  IsFractionRing.map (K := FractionRing (D.ntw.Ok i k)) (L := FractionRing ρ.Oe) ρ.inj

theorem reads_of_pulls {i : D.ntw.Tw} {k : ℕ} {b : Bool} {v : D.what₂.places.Pl} (ρ : Reading i k b v) {Q : Finset (PlE D.host)}
    {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ} {χ : HChar D.host.E} (hp : ρ.Pulls ψ ψ₀)
    (hg : GalOf D χ ψ₀) {ι : FractionRing ρ.Oe →+* ℂ} (hι : ∀ x, ι (ρ.emb x) = D.what₂.embLL x) :
    SideRead i b k (ι.comp (kMap ρ)) ∧ ReadsHecke (ι.comp (kMap ρ)) (ψ.comp (D.ntw.art i Q)) χ := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [RingHom.comp_apply, ← (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D i k b v ρ).2.1 x, hι]
    rfl
  · obtain ⟨-, art, ha, h⟩ := hg
    refine ⟨art, ha, fun x σ e => (h x σ e).trans (Units.ext ?_)⟩
    show D.what₂.embLL (ψ₀ σ : D.what₂.LLˣ) = ι (kMap ρ (algebraMap _ _ ((ψ (D.ntw.art i Q σ) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k)))
    rw [← hι, hp σ]
    simp [IsFractionRing.map]

theorem rank_of_levEq {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m)
    (e : NX.Kk D i k →+* ℂ) (h : LevEq m.J m.χ (cell X b hA j).J (cx e (cell X b hA j).χ)) (hw : CellWt m X b hA j e) :
    Module.finrank D.what₂.LL (D.what₂.MtL μ j') = Module.finrank (NX.Kk D i k) (D.nexp.MtV i (j.1 + 1) b k Q ψ) := by
  haveI : FiniteDimensional (NX.Kk D i k) (D.nexp.MtV i (j.1 + 1) b k Q ψ) := by
    obtain ⟨S, hS⟩ := D.nexp.MtLat_fg i (j.1 + 1) b k Q ψ
    refine ⟨S, ?_⟩
    rw [← D.nexp.MtLat_span i (j.1 + 1) b k Q ψ, ← hS, Submodule.span_span_of_tower]
  have h1 := _root_.GlobalTheory.LevCmp.finrank_typeSp_cx _ _ _ e _ _ _ _ _ (cell X b hA j).χ hw (cell X b hA j).J_open
    (Module.Finite.equiv (cell X b hA j).real)
  rw [(cell X b hA j).real.finrank_eq, ← h1]
  have h2 : NG.TypeSp m.wt.ρ (cell X b hA j).J (cx e (cell X b hA j).χ) = NG.TypeSp m.wt.ρ m.J m.χ := by
    obtain ⟨h3, h4⟩ := h
    ext f
    refine and_congr_right fun _ => ⟨fun H κ => ?_, fun H κ => ?_⟩
    · rw [h4 κ.1 κ.2 (h3 ▸ κ.2)]
      exact H ⟨κ.1, h3 ▸ κ.2⟩
    · rw [← h4 κ.1 (h3.symm ▸ κ.2) κ.2]
      exact H ⟨κ.1, h3.symm ▸ κ.2⟩
  rw [h2, ← m.real_range, LinearMap.finrank_range_of_inj m.real_inj]
  obtain ⟨h3, h4⟩ := D.what₂.jMt_basis μ j' (Module.Free.chooseBasis _ _)
  rw [Module.finrank_eq_nat_card_basis (Module.Free.chooseBasis _ _),
    Module.finrank_eq_nat_card_basis (Module.Basis.mk h3 h4.ge)]

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem muIsW (x : St P) : V4.MuIsW (w.st x.o.Z) f T P.Wt w.I.xi := by
  refine ⟨w.ok.xi_inj, w.xi_range, w.l.xi0, ?_, ?_, P.q.mu.tw, P.q.mu.on, P.q.mu.off,
    P.sub, P.supp⟩
  · show w.I.xi w.I.muStar = f.del
    rw [w.ok.xi_star, w.C_eq]
  · show w.I.xi w.I.muStar' = f.del'
    rw [w.ok.xi_star', w.C_eq]

theorem cfOf_eq (x : St P) : cfOf x = Fr.at (w.st x.o.Z) f :=
  congrArg (Fr.at (w.st x.o.Z)) w.C_eq

theorem exists_tp (x : St P) (C : NChoice (Dof x)) (h : C.Q = QOf P) :
    ∃ tp : TupTied (Dof x) (cfOf x) C, tp.xi = w.I.xi ∧ tp.psi = T.psi := by
  rw [cfOf_eq]
  exact (GlobalTheory.Mem.Top.TupTieW.tupTied_of_muIsW (w.st x.o.Z) f T P.Wt w.I.xi (muIsW x)).2.2.2 C fun v _ =>
    (congrFun h v).trans (Model.qOf_eq v)

theorem disjoint_conductorPlaces_excludedSet {Q : Finset (PlE D.host)} {i : D.ntw.Tw} (h : OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D)))
    (h1 : ∀ u ∈ Q, u ∉ placesOver D.host.E (D.ntw.l i)) (h2 : ∀ u ∈ Q, ∀ p ∈ lowAll D, u ∉ placesOver D.host.E p) :
    Disjoint Q (D.ntw.S0 i) := Finset.disjoint_left.2 fun u hu hS => by
  obtain ⟨p, hp, h3⟩ := h u hS
  rcases Finset.mem_insert.1 hp with rfl | hp
  exacts [h1 u hu h3, h2 u hu p hp h3]

end GlobalTheory.LevCmp

end
