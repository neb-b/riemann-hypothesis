module

public import Formalism.SharpRestriction.GrowthBounds.ChartRank.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.Bundle0002
public import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLift
section
noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PCmpLift

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe Formalism.MainNotions.G.CmpJ.PFormsCl

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

def trN (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (γ0 : GL (Fin (D.R.N i)) D.host.E) :
    (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) →ₗ[ℂ]
      (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) where
  toFun h := fun z => (detF (cTw D i) z)⁻¹ * h (foTrR (embT D) γ0 z)
  map_add' h h' := by funext z; simp only [Pi.add_apply]; ring
  map_smul' a h := by funext z; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem trN_inj (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (γ0 : GL (Fin (D.R.N i)) D.host.E) :
    LinearMap.ker (trN D i hi γ0) = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 fun h hh => ?_
  funext z
  have h1 := congrFun hh (foTrR (embT D) γ0⁻¹ z)
  have h2 : foTrR (embT D) γ0 (foTrR (embT D) γ0⁻¹ z) = z := by
    rw [← foTrR_mul, mul_inv_cancel, foTrR_one]
  change (detF (cTw D i) _)⁻¹ * h (foTrR (embT D) γ0 (foTrR (embT D) γ0⁻¹ z)) = 0 at h1
  rw [h2] at h1
  exact (mul_eq_zero.1 h1).resolve_left (inv_ne_zero (detF_ne _ _))

def phiC (S : StepIn M i hi G) (β : S.Ch) (γ0 : GL (Fin (D.R.N i)) D.host.E) :
    XR (Hc S β).P ℂ →ₗ[ℂ] (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) :=
  (trN D i hi γ0).comp
    (evC (Hc S β).P (S.loc β).rk S.pos (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B))

theorem ker_phiC (S : StepIn M i hi G) (β : S.Ch) (γ0 : GL (Fin (D.R.N i)) D.host.E) : LinearMap.ker (phiC S β γ0) = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 fun Q hQ => ?_
  have h1 : evC (Hc S β).P (S.loc β).rk S.pos (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B) Q = 0 :=
    LinearMap.ker_eq_bot'.1 (trN_inj D i hi γ0) _ hQ
  exact evInj_pf (J := gramN D i hi) (embT D) (Hc S β) (S.loc β) S.pos Q h1

def VtupDesc (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  ∀ β (Q : YR (Hc S β) D.what₂.LL), MvPolynomial.map e Q ∈ (Hc S β).P.Vtup → MvPolynomial.map D.what₂.embLL Q ∈ VtupR (Hc S β).P ℂ

def EvValLe (S : StepIn M i hi G) (β : S.Ch) : Prop :=
  ∀ Q ∈ VtupR (Hc S β).P ℂ,
    evC (Hc S β).P (S.loc β).rk S.pos (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B) Q ∈
      Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (M.lam i)

def CmpInvOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c
    (g : ∀ v, GL (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v)) (γ0 : GL (Fin (D.R.N i)) D.host.E) (κ0 : (S.K β).lev.U),
    γ0 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
    (∀ v, (rep c).2 v = colSpan ((Hc S β).P.W v) (g v : Matrix (Fin ((Hc S β).P.m + 1)) (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v))) →
    (S.loc β).IsPt (rep c).1 g (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 * ((S.K β).y c).1 * κ0.1) →
    ∀ Q ∈ YInv (Hc S β) e (rep c).1 (rep c).2,
      FoInv (S.K β).lev (embT D) ((S.K β).y c) (phiC S β γ0 (MvPolynomial.map D.what₂.embLL Q))

theorem phiC_mem_ValC (S : StepIn M i hi G) (β : S.Ch) (hV : EvValLe S β) (γ0 : GL (Fin (D.R.N i)) D.host.E)
    {Q : XR (Hc S β).P ℂ} (hQ : Q ∈ VtupR (Hc S β).P ℂ) :
    phiC S β γ0 Q ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (lamTG M i) := by
  have h1 := foValC_tr (M.lam i) (Formalism.L2.Forms.atInf (embT D) γ0.1) (foInf_unit (embT D) γ0) (hV Q hQ)
  have h2 := (mem_ValC_shW (D.R.N_pos i) (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (M.lam i) (cTw D i) 1 one_ne_zero
    (phiC S β γ0 Q)).2
  refine h2 ?_
  convert h1 using 1
  funext z
  change 1 * detF (cTw D i) z * ((detF (cTw D i) z)⁻¹ * _) = _
  rw [one_mul, ← mul_assoc, mul_inv_cancel₀ (detF_ne _ _), one_mul]
  rfl

theorem cmpLiftOf_of (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hD : VtupDesc S e) (hV : ∀ β, EvValLe S β)
    (hI : CmpInvOf S e) : CmpLiftOf S e := by
  intro hS H X β rep hok c
  obtain ⟨g, γ0, κ0, hγ0, hL, hpt⟩ := hok c
  let Y := YInv (Hc S β) e (rep c).1 (rep c).2
  let Φ : Y →+ (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) :=
    (phiC S β γ0).toAddMonoidHom.comp ((MvPolynomial.map D.what₂.embLL).toAddMonoidHom.comp Y.subtype.toAddMonoidHom)
  refine ⟨Φ, fun Q => ⟨?_, ?_⟩, fun k Q hQ => ?_⟩
  · exact phiC_mem_ValC S β (hV β) γ0 (hD β Q.1 Q.2.1)
  · exact hI hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q.1 Q.2
  · have a : LinearIndependent D.what₂.LL (fun j => (Q j : YR (Hc S β) D.what₂.LL)) :=
      hQ.map' Y.subtype (Submodule.ker_subtype _)
    have b := Formalism.MainNotions.G.SymmetricFormBlocks.li_map D.what₂.embLL _ a
    exact b.map' (phiC S β γ0) (ker_phiC S β γ0)

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end Formalism.MainNotions.G.CmpJ.PCmpLift
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartRank.NuOfAntiEv
section
open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms

noncomputable section

namespace Formalism.L2.G.EvLe

open Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags Formalism.L2.G.RelativeIndexFlags.Core

theorem nuOf_anti_ev {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (nuOf lam) := by
  intro i j hij
  unfold nuOf
  exact Int.toNat_le_toNat (by have := h hij; omega)

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem vsp_le (v : Fin P.nV) :
    Vsp ℂ (P.lam0 v) ≤ Submodule.span ℂ {Y | ∃ f : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
      (∀ s, f s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
        Y = ∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f s))} := by
  let T : Fin (P.n' v) → Set (MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℂ) := fun s =>
    (fun f => map (Int.castRingHom ℂ) f) '' (weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s)) :
      Set (MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ))
  have hM : ∀ s F, F ∈ (if Antitone (lamAt (P.lam0 v) s) then
      dualWeyl ℂ (P.m + 1) (P.m + 1) (nuOf (lamAt (P.lam0 v) s)) else ⊥) → F ∈ Submodule.span ℂ (T s) := by
    intro s F hF
    have ha := lamAt_anti (P.lam0 v) (P.dom v) s
    rw [if_pos ha, ← Formalism.L2.G.Model.sw_weyl_eq ℂ (P.m + 1) (P.m + 1) le_rfl _ (nuOf_anti_ev ha),
      weyl_eq_span_int] at hF
    exact hF
  have hP := prodSpan (O := ℂ) (I := Fin (P.n' v)) (B := fun _ => MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℂ)
    (fun s => (blockEmb ℂ (S := Fin (P.n' v)) (k := P.m + 1) (n := P.m + 1) s).toLinearMap) T
  unfold Vsp tensorLat
  refine (Submodule.span_mono ?_).trans (hP.le.trans (Submodule.span_mono ?_))
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, fun s => hM s _ (hF s), rfl⟩
  · rintro _ ⟨F, hF, rfl⟩
    choose f hf hfe using fun s => (Set.mem_image _ _ _).1 (hF s)
    exact ⟨f, hf, Finset.prod_congr rfl fun s _ => by rw [← hfe s]; rfl⟩

theorem vtup_le : VtupR P ℂ ≤ Submodule.span ℂ {X | ∃ f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
    (∀ v s, f v s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
      X = ∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f v s)))} := by
  let T : ∀ v : Fin P.nV, Set (MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) ℂ) := fun v =>
    {Y | ∃ f : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
      (∀ s, f s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
        Y = ∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f s))}
  have hP := prodSpan (O := ℂ) (I := Fin P.nV)
    (B := fun v => MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) ℂ)
    (fun v => (rename (R := ℂ) (fun x : Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1)) => (⟨v, x⟩ : Var P))).toLinearMap) T
  unfold VtupR
  refine (Submodule.span_mono ?_).trans (hP.le.trans (Submodule.span_mono ?_))
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, fun v => vsp_le P v (hF v), rfl⟩
  · rintro _ ⟨F, hF, rfl⟩
    have hF' : ∀ v, ∃ f : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
        (∀ s, f s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
          F v = ∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f s)) := hF
    choose f hf hfe using hF'
    exact ⟨f, hf, Finset.prod_congr rfl fun v _ => by rw [hfe v]; rfl⟩

variable {Tau : Type} [Fintype Tau] (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau)

theorem blockRowSubstitution_one (v : Fin P.nV) (s : Fin (P.n' v)) (f : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ) :
    map (RingHom.id ℂ) (bl P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) v s f) = map (Int.castRingHom ℂ) f := by
  have hn : nAt P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) v s = 1 := by
    unfold nAt; split_ifs <;> simp
  have hi : niAt P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) v s = 1 := by
    unfold niAt; split_ifs <;> simp
  unfold bl
  rw [hn, hi, Matrix.det_one, _root_.one_zpow, one_smul, rowAct_one, MvPolynomial.map_id]

theorem gen_mem (G : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (M : Tau → GL (Fin (P.m + 1)) ℂ)
    (lam : Tau → DomWeight (P.m + 1)) (hw : WtTie P rfl pos lam)
    (f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ)
    (hf : ∀ v s, f v s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) :
    evC P rfl pos G (fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ))
      (∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f v s)))) ∈ ValC G lam := by
  choose ft hft hev using fun x : Σ v : Fin P.nV, Fin (P.n' v) =>
    (blk_ev P pos lam M (fun _ => 1) (RingHom.id ℂ) (fun m l _ => oddFact_pf ℤ m l) hw x).1 (f x.1 x.2) (hf x.1 x.2)
  have hX : (∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f v s)))) =
      map (RingHom.id ℂ) (gen P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) f) := by
    rw [map_gen]
    simp only [blockRowSubstitution_one]
  have hM : (fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)) = mcOf M (RingHom.id ℂ) := by
    funext τ; ext a b; rfl
  have key : evC P rfl pos G (mcOf M (RingHom.id ℂ)) (map (RingHom.id ℂ) (gen P rfl pos (fun _ => 1) f)) =
      fnOf G (shiftOf lam) (kcOf M (fun _ => 1) (RingHom.id ℂ))
        (ten fun τ => map (Int.castRingHom ℂ) (ft (pos.symm τ))) := by
    funext z
    refine evC_gen P pos lam M (fun _ => 1) (RingHom.id ℂ) G f (fun τ => ft (pos.symm τ)) (fun x => ?_) z
    show BlockRealisation P pos lam M (fun _ => 1) (RingHom.id ℂ) x (f x.1 x.2) (ft (pos.symm (pos x)))
    rw [pos.symm_apply_apply]
    exact hev x
  have hK : kcOf M (fun _ => 1) (RingHom.id ℂ) = fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) := by
    funext τ; ext a b; simp [kcOf]
  have hP : ten (fun τ => map (Int.castRingHom ℂ) (ft (pos.symm τ))) ∈ CSpan lam := by
    refine Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩
    have h1 := hft (pos.symm τ)
    rw [pos.apply_symm_apply] at h1
    unfold delSq at h1 ⊢
    exact map_mem_weyl le_rfl _ _ h1
  have h0 : fnOf G (shiftOf lam) 1 (ten fun τ => map (Int.castRingHom ℂ) (ft (pos.symm τ))) ∈ ValC G lam :=
    Submodule.mem_map_of_mem hP
  have hu : ∀ τ, IsUnit ((M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)).det := fun τ =>
    (Matrix.isUnit_iff_isUnit_det _).1 (M τ).isUnit
  have h1 := Formalism.MainNotions.G.CmpJ.PFormsCl.foValC_tr lam (fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)) hu h0
  rw [hX, hM, key, hK]
  convert h1 using 1
  funext y
  simp [fnOf, Formalism.MainNotions.G.CmpJ.PFormsCl.foTr]

end Gen

section Main

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ}

theorem evC_le (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (M : Tau → GL (Fin n) ℂ) (lam : Tau → DomWeight n) (hw : WtTie P h pos lam) :
    ∀ Q ∈ VtupR P ℂ, evC P h pos G (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ)) Q ∈ ValC G lam := by
  subst h
  intro Q hQ
  have hS := vtup_le P hQ
  clear hQ
  induction hS using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨f, hf, rfl⟩ := hX
    exact gen_mem P pos G M lam hw f hf
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

end Main

end Formalism.L2.G.EvLe
end
end

