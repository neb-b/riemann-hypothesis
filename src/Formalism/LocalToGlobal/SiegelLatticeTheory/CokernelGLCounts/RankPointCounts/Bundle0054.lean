module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupOrb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0038
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0016

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupLift
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.TupLift

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Pf.TupOrb

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem frame_li {T : E} (F : LFlag S r T) (hT : T ≠ 0) : LinearIndependent E (frame F) := by
  show LinearIndependent E (Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z)
  rw [linearIndependent_finSnoc]
  refine ⟨F.fl.e_indep, fun hz => ?_⟩
  have h0 : ∀ x ∈ Submodule.span E (Set.range F.fl.e), S.hT x F.fl.z = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact F.fl.z_orth a
    | zero => simp
    | add x y _ _ hx hy => simp [map_add (f := _), hx, hy]
    | smul c x _ hx => simp [hx]
  have := h0 _ hz
  rw [F.fl.z_norm] at this
  exact hT (neg_eq_zero.1 this)

theorem nlam_frame_locP {g : ℕ} {Λ : Submodule (𝓞 E) S.V} {T' : E} {F₁ : LFlag S r T'}
    (hL : IsLift Λ F₁) (hC : IsFixedConv Λ g F₁) {m : S.V ≃ₗ[E] S.V} (hm : m ∈ NLam Λ F₁)
    (P : HeightOneSpectrum (𝓞 E)) (hg : (g : 𝓞 E) ∈ P.asIdeal) (b : Fin (r + 1)) :
    m (frame F₁ b) ∈
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 E) (Set.range (frame F₁)))) := by
  have := P.isPrime
  have hA : Formalism.L2.SG.Pf.Apart Λ F₁ ≤
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 E) (Set.range (frame F₁))) := by
    refine sup_le ?_ ?_
    · exact Formalism.L2.SG.Pf.Act.xlam_le_locP Λ g hC P hg (fun a =>
        Formalism.L2.SG.Pf.le_locP' _ _ (Submodule.subset_span ⟨a.castSucc, Formalism.L2.SG.Pf.frame_castSucc_td F₁ a⟩))
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Formalism.L2.SG.Pf.le_locP' _ _
        (Submodule.subset_span ⟨Fin.last _, (Formalism.L2.SG.Pf.frame_last_td F₁).trans hL.2.symm⟩)
  have h0 := Formalism.L2.SG.Pf.frame_mem_locP_Apart hL hC P hg b
  have h1' : m (frame F₁ b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.L2.SG.Pf.Apart Λ F₁) := by
    rw [← Formalism.L2.SG.Pf.NLam_Apart hm hL, Formalism.L2.SG.Pf.gmap_locP]
    exact (Formalism.L2.SG.Pf.gmap_apply_mem m _ _).2 h0
  exact Formalism.L2.SG.Pf.locP_le_locP' hA h1'

theorem coef_int {g : ℕ} {Λ : Submodule (𝓞 E) S.V} {T' : E} {F₁ : LFlag S r T'} (hT : T' ≠ 0)
    (hL : IsLift Λ F₁) (hC : IsFixedConv Λ g F₁) {m : S.V ≃ₗ[E] S.V} (hm : m ∈ NLam Λ F₁)
    {U : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hU : ∀ b, m (frame F₁ b) = ∑ c, U c b • frame F₁ c)
    (P : HeightOneSpectrum (𝓞 E)) (hg : (g : 𝓞 E) ∈ P.asIdeal) (b : Fin (r + 1)) :
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∀ c, ∃ o : 𝓞 E, (s : E) * U c b = (o : E) := by
  have := P.isPrime
  obtain ⟨s, hs, hsm⟩ := nlam_frame_locP hL hC hm P hg b
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hsm
  refine ⟨s, hs, fun c => ⟨o c, ?_⟩⟩
  have hli := frame_li F₁ hT
  have h1 : ∑ c, ((s : E) * U c b) • frame F₁ c = (s : E) • m (frame F₁ b) := by
    rw [hU b, Finset.smul_sum]
    simp only [mul_smul]
  have h2 : ∑ c, ((o c : 𝓞 E) : E) • frame F₁ c = (s : E) • m (frame F₁ b) := by
    rw [← Formalism.L2.SG.Pf.smul_O, ← ho]
    simp only [Formalism.L2.SG.Pf.smul_O]
  have hsum : ∑ c, ((s : E) * U c b - (o c : E)) • frame F₁ c = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h1, h2, sub_self]
  exact sub_eq_zero.1 ((Fintype.linearIndependent_iff.1 hli) _ hsum c)

theorem modG_lift {g : ℕ} {Λ : Submodule (𝓞 E) S.V} {T T' : E} {F : LFlag S r T} {F₁ : LFlag S r T'}
    (hT : T' ≠ 0) (hL : IsLift Λ F₁) (hC : IsFixedConv Λ g F₁) (hFΛ : ∀ c, frame F c ∈ Λ)
    {ν m : S.V ≃ₗ[E] S.V} (hν : IsAutLam S Λ ν) (hm : m ∈ NLam Λ F₁)
    {U U' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hνF : ∀ b, ν (frame F b) = ∑ c, U c b • frame F c) (hmF : ∀ b, m (frame F₁ b) = ∑ c, U' c b • frame F₁ c)
    (hTie : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ c b, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧
      ∃ o : 𝓞 E, (s : E) * (U c b - U' c b) = (g : E) * o)
    (h1 : ∀ c, ModG S Λ g (frame F₁ c - frame F c)) (b : Fin (r + 1)) :
    ModG S Λ g (ν⁻¹ (m (frame F₁ b)) - frame F b) := by
  intro P hg
  have := P.isPrime
  have key : m (frame F₁ b) - ν (frame F b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) := by
    rw [hmF b, hνF b, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ (fun c _ => ?_)
    have e : U' c b • frame F₁ c - U c b • frame F c =
        U' c b • (frame F₁ c - frame F c) + (U' c b - U c b) • frame F c := by
      rw [smul_sub, sub_smul]; abel
    rw [e]
    refine Submodule.add_mem _ ?_ ?_
    · obtain ⟨s, hs, ho⟩ := coef_int hT hL hC hm hmF P hg b
      obtain ⟨o, hoc⟩ := ho c
      obtain ⟨t, ht, htx⟩ := h1 c P hg
      refine ⟨t * s, P.asIdeal.primeCompl.mul_mem ht hs, ?_⟩
      have eq : (t * s) • (U' c b • (frame F₁ c - frame F c)) = o • (t • (frame F₁ c - frame F c)) := by
        rw [Formalism.L2.SG.Pf.smul_O, Formalism.L2.SG.Pf.smul_O, Formalism.L2.SG.Pf.smul_O, smul_smul, smul_smul]
        congr 1
        push_cast
        rw [← hoc]
        ring
      rw [eq]
      exact Submodule.smul_mem _ o htx
    · obtain ⟨s, hs, o, ho⟩ := hTie P hg c b
      refine ⟨s, hs, ?_⟩
      have eq : s • ((U' c b - U c b) • frame F c) = -(o • ((g : 𝓞 E) • frame F c)) := by
        rw [Formalism.L2.SG.Pf.smul_O, Formalism.L2.SG.Pf.smul_O, Formalism.L2.SG.Pf.smul_O, smul_smul, smul_smul, ← neg_smul]
        congr 1
        have : (s : E) * (U' c b - U c b) = -((s : E) * (U c b - U' c b)) := by ring
        rw [this, ho]
        push_cast
        ring
      rw [eq]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ o
        (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hFΛ c)))
  have hinv : IsAutLam S Λ ν⁻¹ := Formalism.L2.SG.Pf.isAutLam_inv hν
  have e : ν⁻¹ (m (frame F₁ b)) - frame F b = ν⁻¹ (m (frame F₁ b) - ν (frame F b)) := by
    rw [map_sub]
    simp [LinearEquiv.coe_inv]
  rw [e]
  have eN : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) =
      Formalism.HermitianLatticesTheory.gmap ν⁻¹ (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ)) := by
    rw [← Formalism.L2.SG.Pf.gmap_locP, Formalism.L2.SG.Pf.gmap_ideal_smul, hinv.2]
  rw [eN]
  exact (Formalism.L2.SG.Pf.gmap_apply_mem ν⁻¹ _ _).2 key

theorem zhat_lift {T T' : E} (F : LFlag S r T) (F₁ : LFlag S r T') {ν m : S.V ≃ₗ[E] S.V}
    (hiso : ∀ x y, S.hT (ν x) (ν y) = S.hT x y) {U U' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hνF : ∀ b, ν (frame F b) = ∑ c, U c b • frame F c) (hmF : ∀ b, m (frame F₁ b) = ∑ c, U' c b • frame F₁ c)
    (a b : Fin (r + 1)) :
    S.hT (frame F a) (ν⁻¹ (m (frame F₁ b))) = (U.conjTranspose * ZhatL F F₁ * U') a b := by
  have e : S.hT (frame F a) (ν⁻¹ (m (frame F₁ b))) = S.hT (ν (frame F a)) (m (frame F₁ b)) := by
    rw [← hiso (frame F a) (ν⁻¹ (m (frame F₁ b)))]
    simp [LinearEquiv.coe_inv]
  rw [e, hνF a, hmF b]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ZhatL, Zhat, brS, map_sum, map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  simp only [RingHom.id_apply]
  ring

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NLamOnto : Prop :=
  ∀ (D : D7) (w : D.what₂.Word) (G : FlagG (VS D) D.R.rS ((Tu D w : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D G Λ → Tu D w ≠ 0 → ∀ U : PairVal.MatR D, IsUpUni U → TupGlob.IntFr U →
      ∃ ν ∈ NLam Λ (lf D G), ∀ b, ν (frame (lf D G) b) = ∑ c, U c b • frame (lf D G) c

variable {D : D7}

theorem isRowLat_of_pd {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ)
    {F₁ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)} (hp : PD D Λ (lf D F0) u' F₁) :
    IsRowLat D F₁.fl Λ :=
  ⟨hΛ.1, ⟨hΛ.2.1.1, hΛ.2.1.2.1, ⟨hp.1.1, rfl⟩, hp.2.2.1⟩, hp.2.2.2⟩

theorem repAtTup_of (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
    (hG : TupGlob.GlobMove D M δ u u') (hO : NLamOnto) : FibPart.RepAtTup M δ u u' F0 what₂ := by
  intro hpre γ w hGw Z hZ hel htup
  have hΛ : IsRowLat D F0 γ.lam := hpre.2.2.2.2.1.1 γ.lam γ.mem
  have hrel : γ.relevant := hpre.2.2.2.2.2 γ w hel
  obtain ⟨x, hx⟩ := hpre.2.2.2.1 γ w hel.2 hrel hel.1.1
  have hex : ∃ y : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) ×
      PairVal.MatR D × PairVal.MatR D, PairVal.NormRep γ y.1 y.2.1 y.2.2.1 y.2.2.2 :=
    ⟨(w, x.1, x.2.1, x.2.2), hx⟩
  have hz : LsDatumB.zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    simp only [LsDatumB.zT, LsDatumB.nrep, dif_pos hex]
  have hspec := hex.choose_spec
  generalize hex.choose = y at hz hspec
  obtain ⟨w₁, F₁, L₁, U₁⟩ := y
  obtain ⟨⟨p₁, e₁⟩, hadm₁, -⟩ := hspec
  simp only at hz
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam hΛ
  have hFun := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam hΛ
  obtain ⟨Fa, ⟨pa, ea⟩, hGa, hcell⟩ := hel.2
  have hdca := (hEq ⟨Fa, pa⟩ ⟨F₁, p₁⟩).1 (ea.trans e₁.symm)
  change DCRel γ.lam (lf D F0) Fa F₁ at hdca
  have hG₁ : Gval (lf D F0) F₁ ≠ 0 := fun h =>
    hGa ((Formalism.L2.SG.Pf.gval_rel (lf D F0) hdca).symm.trans h)
  have hcell₁ : IsInCell (ZhatOM (ZhatL (lf D F0) F₁)) w := (hFun.2.1 ⟨Fa, pa⟩ ⟨F₁, p₁⟩ hdca w).1 hcell
  obtain ⟨Fg, ⟨pg, eg⟩, hgen⟩ := hel.1.1
  have hgen₁ : IsGeneric γ.lam (gS D) (lf D F0) F₁ :=
    (hFun.2.2.2.1 ⟨Fg, pg⟩ ⟨F₁, p₁⟩ ((hEq ⟨Fg, pg⟩ ⟨F₁, p₁⟩).1 (eg.trans e₁.symm))).1 hgen
  have hAt₁ : PCount.AtMat w (ZhatL (lf D F0) F₁) := hcell₁
  have htup' : ∀ p, PCount.tupZ M δ u u' (ZhatL (lf D F0) F₁) p = PCount.tupZ M δ u u' Z p := fun p => by
    rw [← hz]; exact congrFun htup p
  obtain ⟨U, U', hU, hU', hiU, hiU', htie, hZeq⟩ := hG w _ Z hGw hAt₁ hZ htup'
  obtain ⟨ν, hν, hνF⟩ := hO D u F0 γ.lam hΛ hpre.2.2.1.1.ne_zero U hU hiU
  obtain ⟨m, hm, hmF⟩ := hO D u' F₁.fl γ.lam (isRowLat_of_pd hΛ p₁) hpre.2.2.1.2.2.1.ne_zero U' hU' hiU'
  have hm' : m ∈ NLam γ.lam F₁ := hm
  have hmF' : ∀ b, m (frame F₁ b) = ∑ c, U' c b • frame F₁ c := hmF
  have hAut : IsAutLam (VS D) γ.lam (ν⁻¹ * m) :=
    Formalism.L2.SG.Pf.isAutLam_mul (Formalism.L2.SG.Pf.isAutLam_inv hν.1) hm.1
  let F2 := Formalism.L2.SG.Saturated.mapL (ν⁻¹ * m) hAut.1 F₁
  have hf2 : ∀ b, frame F2 b = ν⁻¹ (m (frame F₁ b)) := fun b => by
    rw [Formalism.L2.SG.Saturated.frame_mapL]; rfl
  have hdc : DCRel γ.lam (lf D F0) F₁ F2 :=
    ⟨ν⁻¹, Formalism.L2.SG.Pf.nlamPf_inv hν, m, hm', hf2, rfl⟩
  have pd2 : PD D γ.lam (lf D F0) u' F2 :=
    Formalism.L2.SG.Closed.TermStable_holds D u u' F0 γ.lam hΛ ⟨F₁, p₁⟩ F2 hdc
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hpre.2.2.1.2.2.1.ne_zero
  have hFΛ : ∀ c, frame (lf D F0) c ∈ γ.lam := by
    intro c
    refine Fin.lastCases ?_ (fun a => ?_) c
    · rw [Formalism.L2.SG.Pf.frame_last_td]; exact hΛ.2.1.2.2.1.1
    · rw [Formalism.L2.SG.Pf.frame_castSucc_td]; exact PI.NRL.e_mem_lam D F0 γ.lam hΛ a
  have hiso : ∀ x y, (VS D).hT (ν x) (ν y) = (VS D).hT x y :=
    ((Formalism.L2.SG.Pf.isAutLam_iff γ.lam ν).1 hν.1).1
  have hent : ∀ a b, (VS D).hT (frame (lf D F0) a) (frame F2 b) =
      (U.conjTranspose * ZhatL (lf D F0) F₁ * U') a b := fun a b => by
    rw [hf2 b]; exact zhat_lift (lf D F0) F₁ hiso hνF hmF' a b
  refine ⟨F2, ⟨⟨pd2.1, pd2.2.1, ?_⟩, ?_, ?_, pd2.2.2, ?_⟩,
    pd2, (Quot.sound (show TermDef.Rel γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F₁, p₁⟩ ⟨F2, pd2⟩ from hdc)).symm.trans e₁⟩
  · rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hdc]; exact hG₁
  · refine ⟨fun a b hab => Matrix.one_apply_ne (ne_of_lt hab).symm, fun a => Matrix.one_apply_eq a, fun b => ?_⟩
    rw [frameAct_one', hf2 b]
    exact modG_lift hT' p₁.1 p₁.2.2.1 hFΛ hν.1 hm' hνF hmF' htie
      (fun c => by have := hadm₁.2.2 c; rwa [frameAct_one'] at this) b
  · exact (hFun.2.2.2.1 ⟨F₁, p₁⟩ ⟨F2, pd2⟩ hdc).1 hgen₁
  · have hZZ : ZhatL (lf D F0) F2 = U.conjTranspose * ZhatL (lf D F0) F₁ * U' := by
      funext a b
      exact hent a b
    rw [hZeq]
    exact hZZ

end D7

end Formalism.L2.SG.Pf.TupLift
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.XLeSpanRight
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section T2CR

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def ClaimRL (M : Model F E) (r n : ℕ) : Prop := M.split = none → ClaimR M r n

def ClaimRG (M : Model F E) (r n : ℕ) : Prop := M.split.isSome = true → ClaimR M r n

theorem claimR_of_modes (M : Model F E) (r n : ℕ) (hL : ClaimRL M r n) (hG : ClaimRG M r n) :
    ClaimR M r n := by
  rcases hs : M.split with _ | g
  · exact hL hs
  · exact hG (by rw [hs]; rfl)

theorem X_le_span_left {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.X f ≤ Submodule.span E (Set.range (Sum.elim f f')) :=
  Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨Sum.inl j.castSucc, rfl⟩)

theorem X_le_span_right {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.X f' ≤ Submodule.span E (Set.range (Sum.elim f f')) :=
  Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨Sum.inr j.castSucc, rfl⟩)

theorem surj_MMsharp (M : Model F E) (hM : M.OK) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {r : ℕ} (t : Term V M r) (hgen : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) :
    ∀ m : ↥(MMsharp H t), ∃ w : ↥(H.W0 t.f t.f'), (m : V) + w ∈ t.abelian₂ := by
  intro m
  have hU' : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f')))
      (H.perp (Submodule.span E (Set.range (Sum.elim t.f t.f')))) := by
    rw [← hermSp_W0_eq_perp_span_range_MMfam]
    exact hU
  have hmU : (m : V) ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := spanMM_le_U H t m.2.1
  obtain ⟨x, hx, hpx⟩ := ((local_hermitian_glue F E M hM V H t.abelian₂ hgen.1.1 _ hU').1 (m : V) hmU).2
    (fun y hy hyU => m.2.2 y (hgen.2.2.2 y hy (span_frames_le_MM H t hyU)))
  have hx' : x ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) ⊔
      H.perp (Submodule.span E (Set.range (Sum.elim t.f t.f'))) := by
    rw [hU'.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx'
  have hpa : ((Submodule.linearProjOfIsCompl _ _ hU' x :
      ↥(Submodule.span E (Set.range (Sum.elim t.f t.f')))) : V) = a := by
    rw [← hab, map_add (f := _)]
    have e1 := Submodule.projectionOnto_apply_left hU' ⟨a, ha⟩
    have e2 := Submodule.projectionOnto_apply_right hU' ⟨b, hb⟩
    simp only [Submodule.linearProjOfIsCompl] at *
    rw [e1, e2, add_zero]
  have hma : (m : V) = a := by rw [← hpx, hpa]
  have hbW : b ∈ H.W0 t.f t.f' := by rw [hermSp_W0_eq_perp_span_range_MMfam]; exact hb
  refine ⟨⟨b, hbW⟩, ?_⟩
  show (m : V) + b ∈ t.abelian₂
  rw [hma, hab]
  exact hx

theorem claimRL_at (M : Model F E) (r n : ℕ) (hM : M.OK) : ClaimRL M r n := by
  intro hs V _ _ H hn t₁ f₂ f₂' φ φ' hyp Λ₂ hg hth θ hθ
  have hT₁ := hyp.1.1
  have hT₂ := hg.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hT₁.2.1.2.1, hT₁.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hT₁.2.2.1.2.1, hT₁.2.2.1.2.2.1⟩
  have hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)) := hT₂.2.2.2.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT₁.2.2.2.1
  obtain ⟨ψ, -, hψc⟩ := corrIso_holds M r n V H hn t₁ f₂ f₂' φ φ' hyp hD₂
  have hU₁ : IsCompl (Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (H.W0 t₁.f t₁.f') :=
    isCompl_span_frames_W0 H t₁.f t₁.f' t₁.T t₁.T' hF₁ hF₁' hD₁ (isUnit_Gdet H _ _ _ _ hT₁.2.2.2.2.1)
  have hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim f₂ f₂'))) (H.W0 f₂ f₂') :=
    isCompl_span_frames_W0 H f₂ f₂' t₁.T t₁.T' hyp.2.1 hyp.2.2.1 hD₂ (isUnit_Gdet H _ _ _ _ hT₂.2.2.2.2.1)
  have hMM₁ : MMo H t₁ ≤ t₁.abelian₂ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hyp.1.2.1 i)
  have hMM₂ : MMo H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) ≤ Λ₂ :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hg.2.1 i)
  have hth' : ∀ w : ↥(H.W0 t₁.f t₁.f'), (w : V) ∈ t₁.abelian₂ ↔ (ψ w : V) ∈ Λ₂ :=
    fun w => hth w (ψ w) ((hψc _ _).2 ⟨w.2, rfl⟩)
  have hθ' : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) m₂ ↔
      ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂ ∧ (m₂ : V) + ψ w ∈ Λ₂ := by
    intro m₁ m₂
    rw [hθ m₁ m₂]
    constructor
    · rintro ⟨n₁, n₂, hc, h1, h2⟩
      obtain ⟨hn₁, hψn⟩ := (hψc _ _).1 hc
      exact ⟨⟨n₁, hn₁⟩, h1, by rw [hψn]; exact h2⟩
    · rintro ⟨w, h1, h2⟩
      exact ⟨w, ψ w, (hψc _ _).2 ⟨w.2, rfl⟩, h1, h2⟩
  have hsurj₁ := surj_MMsharp M hM H t₁ hyp.1 hU₁

  have hC1 : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ (H.mkW t₁.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩) = H.mkW f₂ ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp H (ψ w).2⟩ := by
    intro w
    obtain ⟨_, _, c₁, _⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
    exact c₁
  have hC1' : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ' (H.mkW t₁.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩) = H.mkW f₂' ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp' H (ψ w).2⟩ := by
    intro w
    obtain ⟨_, _, _, c₂⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
    exact c₂
  have hZ₁ : IsUnit (H.Zhat t₁.f t₁.f').det := by rw [← Dl_succ]; exact hD₁
  have hZ₁' : IsUnit (H.Zhat t₁.f' t₁.f).det := det_Zhat_swap_unit H _ _ hZ₁
  have hzφ : φ (H.mkW t₁.f ⟨t₁.f (Fin.last r), z_mem_perpX H hF₁⟩) =
      H.mkW f₂ ⟨f₂ (Fin.last r), z_mem_perpX H hyp.2.1⟩ := by
    have e := hyp.2.2.2.2.1 ⟨_, z_mem_perpX H hF₁⟩ ⟨_, z_mem_perpX H hyp.2.1⟩ rfl rfl
    simpa using e
  have hzφ' : φ' (H.mkW t₁.f' ⟨t₁.f' (Fin.last r), z_mem_perpX H hF₁'⟩) =
      H.mkW f₂' ⟨f₂' (Fin.last r), z_mem_perpX H hyp.2.2.1⟩ := by
    have e := hyp.2.2.2.2.2 ⟨_, z_mem_perpX H hF₁'⟩ ⟨_, z_mem_perpX H hyp.2.2.1⟩ rfl rfl
    simpa using e
  obtain ⟨u, hu⟩ := hD₂
  have hoφ : φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
      ((↑u⁻¹ : E) * H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ := by
    have e : H.Dl f₂ f₂' (r + 1) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
        H.Dl t₁.f t₁.f' (r + 1) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.1 _ _ rfl rfl
    rw [← hu] at e
    calc φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)
        = (↑u⁻¹ : E) • ((u : E) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  obtain ⟨u', hu'⟩ : IsUnit (M.L.cj (H.Dl f₂ f₂' (r + 1))) := by rw [← hu]; exact (Units.isUnit u).map _
  have hoφ' : φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
      ((↑u'⁻¹ : E) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1))) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ := by
    have e : M.L.cj (H.Dl f₂ f₂' (r + 1)) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
        M.L.cj (H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.2.1 _ _ (om'_swap H _ _) (om'_swap H _ _)
    rw [← hu'] at e
    calc φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)
        = (↑u'⁻¹ : E) • ((u' : E) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  have hC2 := cond_second_of_iso H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T hF₁ hyp.2.1 hZ₁ φ _ hzφ hoφ
  have hC2'' := cond_second_of_iso H t₁.f' t₁.f f₂' f₂ t₁.T' t₁.T' hF₁' hyp.2.2.1 hZ₁' φ' _ hzφ' hoφ'
  have hC2' : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X t₁.f'),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim f₂ f₂')), ∃ hu' : u' ∈ H.perp (H.X f₂'),
        φ' (H.mkW t₁.f' ⟨u, hu⟩) = H.mkW f₂' ⟨u', hu'⟩ := by
    intro v hv hvp
    rw [← U_swap] at hv
    obtain ⟨v', hv', hv'p, e⟩ := hC2'' v hv hvp
    rw [U_swap] at hv'
    exact ⟨v', hv', hv'p, e⟩
  have hL := claimR_side H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ ψ hU₂ hU₁ hT₁.1 hT₂.1 hMM₁ hMM₂ hth' θ hθ' hsurj₁
    t₁.f f₂ (X_le_span_left H f₂ f₂') (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp H h) (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp H h) φ hC1 hC2
  have hL' := claimR_side H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ ψ hU₂ hU₁ hT₁.1 hT₂.1 hMM₁ hMM₂ hth' θ hθ' hsurj₁
    t₁.f' f₂' (X_le_span_right H f₂ f₂') (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp' H h) (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp' H h) φ' hC1' hC2'
  constructor
  · intro hR
    refine ⟨fun _ => ⟨hL.1 hR.1, hL'.1 hR.2.2.1⟩, fun g hg => ?_⟩
    rw [hs] at hg
    exact absurd hg (by simp)
  · rintro ⟨h1, -⟩
    obtain ⟨a, b⟩ := h1 hs
    refine ⟨hL.2 a, hyp.2.2.2.2.1, hL'.2 b, hyp.2.2.2.2.2, fun g hg => ?_⟩
    rw [hs] at hg
    exact absurd hg (by simp)

end T2CR

end Formalism.L2.SG.LsDatumA
end
end

