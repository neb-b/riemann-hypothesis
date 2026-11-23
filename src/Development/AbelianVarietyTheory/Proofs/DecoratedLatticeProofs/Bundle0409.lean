module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0385
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralMatrixSplitPlaceMemStdHomLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_matrix_split_place_mem_stdHomLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (a₀ : D.host.E), a₀ ∈ (D.host.AA : Set D.host.E) → q.pr (incA D a₀) ≠ 0 → ∀ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), FT.β = 1 → FT.γ = 1 → FS.γ = q.pr (incA D a₀) • (HSpace.gram S).map (fun a => q.pr (incA D a)) → ∀ t : Matrix (Fin T.rank) (Fin S.rank) k, (∀ r s, t r s ∈ 𝒪[k]) → (Place.ofSplitPt q).up FS FT t ∈ stdHom S T := by
  first | exact @GlobalTheory.SplitUpStd.int_up_mem_stdHom | exact GlobalTheory.SplitUpStd.int_up_mem_stdHom | (intros; apply GlobalTheory.SplitUpStd.int_up_mem_stdHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfAddCharTrivialOnHomLatticeLine
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.InvLat

open GlobalTheory.FinPl.SuppShift

variable {D : D7}

theorem single_mul_mul_single {ρ : ℕ} (M : Mx D ρ ρ) (i : Fin ρ) :
    (Matrix.single i i 1 : Mx D ρ ρ) ⬝ (M ⬝ (Matrix.single i i 1 : Mx D ρ ρ)) = Matrix.single i i (M i i) := by
  rw [← Matrix.mul_assoc, Matrix.single_mul_mul_single, one_mul, mul_one]

theorem pairS_single {W W₀ : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ) (i : Fin ρ) (c : AE D) (x : Mx D W.rank ρ) :
    pairS W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) x = cA D ((dW.pY ⬝ x) i i) * c := by
  have h : adj (dW.pY ⬝ x) = adj x ⬝ (gA W ⬝ dW.jX) := by
    rw [dW.pY_eq, adj_mul, adj_mul, adj_adj, adj_gA]
  rw [pairS, ← Matrix.mul_assoc (gA W), ← Matrix.mul_assoc, ← h, Matrix.trace_mul_single, op_smul_eq_mul]
  rfl


set_option maxHeartbeats 1600000 in
theorem int_of_psi_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : Pl D), Tame D v → IsSelfDualC V LV → IsSelfDualC W LW → MonoAt dV LV LV₀ v → MonoAt dW LW LW₀ v → ColsAt dV dW.jX LV LW v → ∀ (i : Fin ρ) (c : AE D), c - 1 ∈ idAt D (· = v) → (∀ b ∈ idAt D (· = v), dV.extY W (dW.jY ⬝ Matrix.single i i b) ∈ latO V W (LV : Set _) (LW : Set _) (· = v) → ψ (symplO V W (dV.extX W (dW.jX ⬝ Matrix.single i i c)) (dV.extY W (dW.jY ⬝ Matrix.single i i b))) = 1) → c - 1 ∈ intAt D (· = v) := by
  intro D ψ hψ V V₀ W W₀ ρ dV dW LV LV₀ LW LW₀ v _ hV hW hmV hmW hcols i c hc1 hyp
  have hU : SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) ∈
      latO V W (LV : Set _) (LW : Set _) (· = v) := by
    refine (SelfDualAt.latO_ann_at D ψ hψ V W LV LW hV hW (· = v) _ fun k l => ?_).2 fun u hu => ?_
    · rw [Matrix.smul_apply, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (eps_idAt v)
    have hux := LatMem.latO_mxAt hu
    have hfixu : SelfDualAt.cP (· = v) • u = u := by
      ext k l
      rw [Matrix.smul_apply, Algebra.smul_def]
      exact eps_mul (hux k l)
    have hπ := sandwich_latO hV hW (dW.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dW.pY) (fun z hz => by
        rw [← Matrix.mulVec_mulVec, single_mulVec', one_mul]
        exact ((hmW z).1 hz).2.1 i)
      (dV.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dV.pY) (fun z hz => by
        rw [← Matrix.mulVec_mulVec, single_mulVec', one_mul]
        exact ((hmV z).1 hz).2.1 i) hu
    have e : dW.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dW.pY ⬝ (u ⬝ (dV.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dV.pY)) =
        dV.extY W (dW.jY ⬝ (Matrix.single i i ((dW.pY ⬝ (u ⬝ dV.jY)) i i) : Mx D ρ ρ)) := by
      rw [HypDec.extY_apply, ← single_mul_mul_single]
      simp only [Matrix.mul_assoc]
    rw [e] at hπ
    have h1 := hyp _ (mxAt_mul_left dW.pY (mxAt_mul_right hux dV.jY) i i) hπ
    rw [symplO_eq, hO_extX, pairS_single, HypDec.extY_apply, Matrix.mul_assoc, dV.pY_jY, Matrix.mul_one,
      ← Matrix.mul_assoc dW.pY dW.jY, dW.pY_jY, Matrix.one_mul, Matrix.single_apply_same] at h1
    rw [← SelfDualAt.symplO_smul_swap, hfixu, symplO_eq, hO_extX, pairS_single]
    exact h1
  have hint : finPart D c ∈ intAE D := by
    refine int_of_stable dV hV hmV i hc1 fun a ha => ?_
    have ha' := idAt_of_colMul dV ha
    have h := LatMem.latO_maps hV hU ha
    have e : (SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ))) *ᵥ colMul dV.jX i a =
        colMul dW.jX i (c * a) := by
      have e0 : SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) =
          eps v • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) := by
        ext k l
        rw [Matrix.smul_apply, Algebra.smul_def]
        rfl
      rw [e0, Matrix.smul_mulVec, HypDec.extX_apply, ← Matrix.mulVec_mulVec, single_mulVec', pX_colMul,
        ← colMul_mul, eps_mul (Ideal.mul_mem_left _ _ ha')]
    rw [e] at h
    exact (hcols i _ (Ideal.mul_mem_left _ _ ha')).2 h
  refine ⟨hc1, ?_⟩
  rw [RingHom.map_sub]
  exact sub_mem hint (int_of_idem (one_mul 1))

end GlobalTheory.FinPl.InvLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactOpenProductLevelsFamily
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

namespace GlobalTheory.QVal.LevCO

variable {D : D7}

theorem isCO_iSup_map (V : HSp D) {r : ℕ} (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i))
    (hq : Function.Injective fun i => (q i).v) (Y : Fin r → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (F : ∀ i, GlobalTheory.LocMod.Frame (k i) V.rank (Y i)) (gl : ∀ i, GL (Y i) (k i) →* GA D V)
    (hgl : ∀ i g, SuppAt (q i).e V (gl i g) ∧ (mt V (gl i g)).map (q i).pr = (F i).β * g.val * (F i).γ)
    (L : ∀ i, Subgroup (GL (Y i) (k i))) (hL : ∀ i, IsCO (L i)) :
    IsCO ((⨆ i, (L i).map (gl i)).subgroupOf (GlobalTheory.FinPl.grpAt V (fun p => ∃ i, (q i).v = p))) := by
  set P : GlobalTheory.FinPl.Pl D → Prop := fun p => ∃ i, (q i).v = p with hPdef
  have hA : GlobalTheory.FinPl.grpAt V P = GlobalTheory.FinPl.grpAt V (fun p => ∃ i, p = (q i).v) := by
    congr 1
    funext p
    exact propext ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩
  obtain ⟨Ψ, hc, -, -, huniq⟩ := GlobalTheory.FixLev.exists_section V k q hq Y F
  let lh : ∀ i, GA D V →* GL (Y i) (k i) := fun i => GlobalTheory.FixLev.locHom (q i) V (F i)
  have hlh_self : ∀ i g, lh i (gl i g) = g := fun i g =>
    Units.ext (GlobalTheory.FixLev.frame_cancel (F i) ((GlobalTheory.FixLev.locHom_spec _ _ _ _).symm.trans (hgl i g).2))
  have hmat_ne : ∀ i j, i ≠ j → ∀ g, (mt V (gl j g)).map (q i).pr = 1 := fun i j hij g =>
    _root_.GlobalTheory.OtherPlace.mt_map_pr_eq_one D (k i) (k j) (q i) (q j) V (gl j g) (fun e => hij (hq e)) (hgl j g).1
  have hlh_ne : ∀ i j, i ≠ j → ∀ g, lh i (gl j g) = 1 := fun i j hij g => Units.ext (by
    show (F i).γ * (mt V (gl j g)).map (q i).pr * (F i).β = 1
    rw [hmat_ne i j hij g, Matrix.mul_one, (F i).γβ])
  set H := ⨆ i, (L i).map (gl i) with hHdef
  have hglA : ∀ i g, gl i g ∈ GlobalTheory.FinPl.grpAt V P := fun i g =>
    _root_.GlobalTheory.SuppGrp.mem_grpAt_of_suppAt D (k i) (q i) V _ (hgl i g).1 P ⟨i, rfl⟩
  have hHL : ∀ x ∈ H, ∀ i, lh i x ∈ L i := by
    intro x hx i
    have hle : H ≤ (L i).comap (lh i) := iSup_le fun j => Subgroup.map_le_iff_le_comap.2 fun g hg => by
      show lh i (gl j g) ∈ L i
      by_cases hij : i = j
      · subst hij
        rw [hlh_self]
        exact hg
      · rw [hlh_ne i j hij]
        exact one_mem _
    exact hle hx
  let Φ : (∀ i, GL (Y i) (k i)) → GA D V := fun y => ((List.finRange r).map fun i => gl i (y i)).prod
  have hΦA : ∀ y, Φ y ∈ GlobalTheory.FinPl.grpAt V P := fun y =>
    Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
      exact hglA i (y i)
  have hΦH : ∀ y, (∀ i, y i ∈ L i) → Φ y ∈ H := fun y hy =>
    Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
      exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_map_of_mem _ (hy i))
  have hΦloc : ∀ y i, (mt V (Φ y)).map (q i).pr = (F i).β * (y i).val * (F i).γ := fun y i => by
    show (mt V ((List.finRange r).map fun i => gl i (y i)).prod).map (q i).pr = _
    rw [GlobalTheory.FixLev.map_mt_list_prod, List.map_map]
    exact (GlobalTheory.FixLev.list_prod_single (fun i' => (mt V (gl i' (y i'))).map (q i).pr) i
      (fun i' hi' => hmat_ne i i' (Ne.symm hi') _) _ (List.nodup_finRange r) (List.mem_finRange i)).trans
      (hgl i (y i)).2
  have hΨΦ : ∀ y, Ψ y = Φ y := fun y => huniq (Φ y) (by rw [← hA]; exact hΦA y) y (hΦloc y)
  have hx_eq : ∀ x ∈ GlobalTheory.FinPl.grpAt V P, Ψ (fun i => lh i x) = x := fun x hx =>
    huniq x (by rw [← hA]; exact hx) _ fun i => GlobalTheory.FixLev.locHom_spec _ _ _ x
  have hmem : ∀ x : GlobalTheory.FinPl.grpAt V P, (x : GA D V) ∈ H ↔ ∀ i, lh i x ∈ L i := fun x =>
    ⟨fun h => hHL _ h, fun h => by rw [← hx_eq x x.2, hΨΦ]; exact hΦH _ h⟩
  refine ⟨?_, ?_⟩
  · have hset : ((H.subgroupOf (GlobalTheory.FinPl.grpAt V P) : Subgroup _) : Set (GlobalTheory.FinPl.grpAt V P)) =
        ⋂ i, (fun g : GlobalTheory.FinPl.grpAt V P => lh i g.1) ⁻¹' (L i : Set _) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_iInter, Set.mem_preimage]
      exact hmem g
    rw [hset]
    exact isOpen_iInter_of_finite fun i =>
      (hL i).1.preimage ((GlobalTheory.FixLev.continuous_locHom _ _ _).comp continuous_subtype_val)
  · rw [Subtype.isCompact_iff]
    have himg : (((↑) : GlobalTheory.FinPl.grpAt V P → GA D V) ''
        ((H.subgroupOf (GlobalTheory.FinPl.grpAt V P) : Subgroup _) : Set (GlobalTheory.FinPl.grpAt V P))) =
        Ψ '' Set.pi Set.univ fun i => (L i : Set _) := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : (x : GA D V) ∈ H := Subgroup.mem_subgroupOf.1 hx
        exact ⟨fun i => lh i x, fun i _ => hHL _ hx' i, hx_eq x x.2⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨⟨Ψ y, ?_⟩, ?_, rfl⟩
        · rw [hΨΦ]
          exact hΦA y
        · show Ψ y ∈ H
          rw [hΨΦ]
          exact hΦH y fun i => hy i (Set.mem_univ _)
    rw [himg]
    exact (isCompact_univ_pi fun i => (hL i).2).image hc

theorem isCO_levJ_levB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin r → QStep S),
    Function.Injective (fun i => (Q i).q.v) → IsCO (levJ Q) ∧ IsCO (levB Q) := by
  intro D ψ σ S r Q hinj
  exact ⟨isCO_iSup_map S.J.W (fun i => (Q i).k) (fun i => (Q i).q) hinj _ (fun i => (Q i).F.G₁) (fun i => (Q i).gl₁)
      (fun i g => (Q i).loc₁ g) (fun i => (Q i).L₁.J) (fun i => (Q i).co₁),
    isCO_iSup_map S.B'.V (fun i => (Q i).k) (fun i => (Q i).q) hinj _ (fun i => (Q i).F.G₂) (fun i => (Q i).gl₂)
      (fun i g => (Q i).loc₂ g) (fun i => (Q i).L₂.J) (fun i => (Q i).co₂)⟩

end GlobalTheory.QVal.LevCO

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFrameFinitePartMulOfCarriesLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.Core.Mi.FrameMove

variable {D : D7}

theorem finPart_finIn' (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    finPart D (GlobalTheory.FinPlLoc.finIn D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e =>
    rw [GlobalTheory.FinPlLoc.finIn_tmul]
    unfold finPart
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem finIn_mem_idAt (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    GlobalTheory.FinPlLoc.finIn D z ∈ idAt D (fun _ => True) := by
  refine Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (GlobalTheory.FinPlLoc.infPart_finIn z), ?_⟩
  exact (Submodule.mem_iInf _).2 fun w => absurd trivial w.2

theorem mulVec_mem_ideal {I : Ideal (AE D)} {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) (k : Fin m) : (A *ᵥ y) k ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun i _ => I.mul_mem_left _ (hy i)

theorem finE_mulVec_hat (S : HSp D) (x : GA D S) (y : Fin S.rank → AE D) :
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((mt S x *ᵥ y) i))) =
      (Formalism.IndefR.Lev.finE S x).val *ᵥ (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) := by
  have h : ((Formalism.IndefR.Lev.finE S x).val) = (mt S x).map ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) := by
    ext i j
    rfl
  rw [h]
  ext i
  exact RingHom.map_mulVec ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) (mt S x) y i

theorem hat_iff_of_moves (V : HSp D) (t : GA D V) (Λ M : Lat V) (hm : Moves V t Λ M (fun _ => True))
    (z : Fin V.rank → Formalism.IndefR.Lev.EAf D) :
    z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      (Formalism.IndefR.Lev.finE V t).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M := by
  let sw := Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E
  let y : Fin V.rank → AE D := fun i => GlobalTheory.FinPlLoc.finIn D (sw.symm (z i))
  have hy : ∀ i, y i ∈ idAt D (fun _ => True) := fun i => finIn_mem_idAt _
  have hz : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) = z := by
    funext i
    show Formalism.IndefR.Lev.swapAE D (finPart D (GlobalTheory.FinPlLoc.finIn D (sw.symm (z i)))) = z i
    rw [finPart_finIn']
    exact sw.apply_symm_apply (z i)
  have hy' : ∀ i, (mt V t *ᵥ y) i ∈ idAt D (fun _ => True) := mulVec_mem_ideal _ hy
  rw [← hz, ← finE_mulVec_hat]
  constructor
  · intro h
    have h1 : y ∈ latV V Λ (fun _ => True) := GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ y hy h
    exact GlobalTheory.LatVHat.latV_mem_hatL D V M _ _ ((hm y hy).1 h1)
  · intro h
    have h1 : mt V t *ᵥ y ∈ latV V M (fun _ => True) := GlobalTheory.HatLatV.mem_latV_of_hatL D V M _ _ hy' h
    exact GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ y ((hm y hy).2 h1)

theorem isFrame_of_moves : ∀ (D : D7) (V : HSp D) (t : GA D V) (Λ M : Lat V)
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)), Moves V t Λ M (fun _ => True) → Formalism.L2.DIV.IsFrame β Λ →
    Formalism.L2.DIV.IsFrame (finE V t * β) M := by
  intro D V t Λ M β hm hf x
  have e1 : (finE V t).val *ᵥ (((finE V t)⁻¹).val *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have k := hat_iff_of_moves V t Λ M hm (((finE V t)⁻¹).val *ᵥ x)
  rw [e1] at k
  change x ∈ Formalism.L2.Herm.hatL (F := D.host.F) M ↔ _
  rw [← k, hf, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]

end GlobalTheory.Core.Mi.FrameMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMulLeftInvariantMapLevyProductMapToFourierJaco
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR.LeftFJ

open GlobalTheory.RootEx

section Alg
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def conjN (p : ℕ) (g : GL n k) (u' : N k n c p) : N k n c p :=
  ⟨embX c g⁻¹ * (u' : GL (n ⊕ Fin c) k) * (embX c g⁻¹)⁻¹,
    ((Radical.unipotent_radical_basic k n c p).2.2.2.1 g⁻¹ u' u'.2).1⟩

theorem mul_prodRFJ_embX (ρ : ℕ) (g' : GL n k) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) :
    embX c g' * (prodRFJ ρ q : GL (n ⊕ Fin c) k) = prodRFJ ρ ((g' * q.1.1, q.1.2), q.2) := by
  simp only [prodRFJ_coe, map_mul, mul_assoc]

theorem mul_prodRFJ_N (ρ : ℕ) (u' : N k n c (ρ + 1)) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) :
    (u' : GL (n ⊕ Fin c) k) * (prodRFJ ρ q : GL (n ⊕ Fin c) k) =
      prodRFJ ρ ((q.1.1, conjN (ρ + 1) q.1.1 u' * q.1.2), q.2) := by
  simp only [prodRFJ_coe, conjN, Subgroup.coe_mul, map_inv, inv_inv]
  group

theorem mul_prodRFJ_colE (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β' : n → k)
    (q : (GL n k × N k n c (ρ + 1)) × (n → k)) :
    colE c (ρ + 1) β' * (prodRFJ ρ q : GL (n ⊕ Fin c) k) =
      prodRFJ ρ ((q.1.1, cjE ρ h1 h2 (((q.1.1)⁻¹ : GL n k).val *ᵥ β') q.1.2),
        ((q.1.1)⁻¹ : GL n k).val *ᵥ β' + q.2) := by
  obtain ⟨⟨g, u⟩, β⟩ := q
  set γ := ((g)⁻¹ : GL n k).val *ᵥ β'
  have hc : colE c (ρ + 1) β' = embX c g * colE c (ρ + 1) γ * (embX c g)⁻¹ := by
    rw [QuotStep.conj_colE]
    congr 1
    simp only [γ, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [prodRFJ_coe, prodRFJ_coe, cjE_coe, hc, ← FourierJacobiGroup.colE_add]
  group

end Alg

section Meas
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem continuous_conjN (p : ℕ) (u' : N k n c p) : Continuous fun g : GL n k => conjN p g u' := by
  have he := QuotStep.continuous_embX (k := k) (n := n) (c := c)
  refine Continuous.subtype_mk ?_ _
  exact ((he.comp continuous_inv).mul continuous_const).mul (he.comp continuous_inv).inv

theorem continuous_cjE (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) :
    Continuous fun x : (n → k) × N k n c (ρ + 1) => cjE ρ h1 h2 x.1 x.2 := by
  have hc := QuotStep.continuous_colE (k := k) (n := n) (c := c) (ρ + 1)
  refine Continuous.subtype_mk ?_ _
  exact ((hc.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).mul
    (hc.comp continuous_fst).inv

theorem continuous_prodRFJ (ρ : ℕ) : Continuous (prodRFJ (k := k) (n := n) (c := c) ρ) := by
  have he := QuotStep.continuous_embX (k := k) (n := n) (c := c)
  have hc := QuotStep.continuous_colE (k := k) (n := n) (c := c) (ρ + 1)
  refine Continuous.subtype_mk ?_ _
  exact ((he.comp (continuous_fst.comp continuous_fst)).mul
    (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).mul (hc.comp continuous_snd)

theorem continuous_invMulVec (β' : n → k) : Continuous fun g : GL n k => ((g⁻¹ : GL n k)).val *ᵥ β' :=
  (Units.continuous_val.comp continuous_inv).matrix_mulVec continuous_const

end Meas

theorem map_mul_left_of_conj {Q G : Type} [MeasurableSpace Q] [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure Q) (f : Q → G) (hf : Measurable f) (h : G) (T : Q → Q) (hT : MeasurePreserving T μ μ)
    (he : ∀ q, h * f q = f (T q)) : (μ.map f).map (h * ·) = μ.map f := by
  rw [Measure.map_map (measurable_const_mul h) hf]
  have : (fun x => h * x) ∘ f = f ∘ T := funext he
  rw [this, ← Measure.map_map hf hT.measurable, hT.map_eq]

theorem map_mul_left_mul {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (κ : Measure G)
    (a b : G) (ha : κ.map (a * ·) = κ) (hb : κ.map (b * ·) = κ) : κ.map ((a * b) * ·) = κ := by
  have : (fun x => a * b * x) = (fun x => a * x) ∘ (fun x => b * x) := funext fun x => mul_assoc a b x
  rw [this, ← Measure.map_map (measurable_const_mul a) (measurable_const_mul b), hb, ha]

section Kinds
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  [SecondCountableTopology k] [BorelSpace (GL n k)] [SecondCountableTopology (GL n k)]
  [BorelSpace (GL (n ⊕ Fin c) k)] [SecondCountableTopology (GL (n ⊕ Fin c) k)]

def fibFJ (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β' : n → k) (g : GL n k) (x : N k n c (ρ + 1) × (n → k)) :
    N k n c (ρ + 1) × (n → k) :=
  (cjE ρ h1 h2 (((g⁻¹ : GL n k)).val *ᵥ β') x.1, ((g⁻¹ : GL n k)).val *ᵥ β' + x.2)

theorem measurable_fibFJ (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β' : n → k) :
    Measurable (Function.uncurry (fibFJ ρ h1 h2 β')) := by
  have hγ : Continuous fun p : GL n k × (N k n c (ρ + 1) × (n → k)) => ((p.1⁻¹ : GL n k)).val *ᵥ β' :=
    (continuous_invMulVec β').comp continuous_fst
  have hc : Continuous fun p : GL n k × (N k n c (ρ + 1) × (n → k)) =>
      (cjE ρ h1 h2 (((p.1⁻¹ : GL n k)).val *ᵥ β') p.2.1, ((p.1⁻¹ : GL n k)).val *ᵥ β' + p.2.2) :=
    ((continuous_cjE ρ h1 h2).comp (hγ.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (hγ.add (continuous_snd.comp continuous_snd))
  exact hc.measurable

theorem map_fibFJ (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure]
    [SFinite (volN ν n c (ρ + 1))] (β' : n → k) (g : GL n k) :
    ((volN ν n c (ρ + 1)).prod (Measure.pi fun _ : n => ν)).map (fibFJ ρ h1 h2 β' g) =
      (volN ν n c (ρ + 1)).prod (Measure.pi fun _ : n => ν) := by
  have e : fibFJ ρ h1 h2 β' g = Prod.map (cjE ρ h1 h2 (((g⁻¹ : GL n k)).val *ᵥ β'))
      (fun β => ((g⁻¹ : GL n k)).val *ᵥ β' + β) := rfl
  have hcm : Measurable (cjE ρ h1 h2 (((g⁻¹ : GL n k)).val *ᵥ β')) :=
    ((continuous_cjE ρ h1 h2).comp (continuous_const.prodMk continuous_id)).measurable
  rw [e, ← Measure.map_prod_map _ _ hcm (measurable_const_add _), _root_.GlobalTheory.HaarR.map_volN_cjE k n c ρ h1 h2 ν inferInstance,
    map_add_left_eq_self]

theorem mp_colE (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure]
    [SFinite (volN ν n c (ρ + 1))] (m : Measure (GL n k)) [SFinite m] (β' : n → k) :
    MeasurePreserving (fun q : (GL n k × N k n c (ρ + 1)) × (n → k) =>
      ((q.1.1, cjE ρ h1 h2 (((q.1.1)⁻¹ : GL n k).val *ᵥ β') q.1.2), ((q.1.1)⁻¹ : GL n k).val *ᵥ β' + q.2))
      ((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν))
      ((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)) := by
  have hA := measurePreserving_prodAssoc m (volN ν n c (ρ + 1)) (Measure.pi fun _ : n => ν)
  have hs := (MeasurePreserving.id m).skew_product (measurable_fibFJ ρ h1 h2 β')
    (Filter.Eventually.of_forall (map_fibFJ ρ h1 h2 ν β'))
  exact (MeasurePreserving.symm _ hA).comp (hs.comp hA)

theorem mp_N (ρ : ℕ) (ν : Measure k) [ν.IsAddHaarMeasure] (V : Measure (N k n c (ρ + 1)))
    [V.IsMulLeftInvariant] [SFinite V] (m : Measure (GL n k)) [SFinite m] (u' : N k n c (ρ + 1)) :
    MeasurePreserving (fun q : (GL n k × N k n c (ρ + 1)) × (n → k) =>
      ((q.1.1, conjN (ρ + 1) q.1.1 u' * q.1.2), q.2))
      ((m.prod V).prod (Measure.pi fun _ : n => ν)) ((m.prod V).prod (Measure.pi fun _ : n => ν)) := by
  have hm2 : Measurable (Function.uncurry fun (g : GL n k) (u : N k n c (ρ + 1)) => conjN (ρ + 1) g u' * u) :=
    (((continuous_conjN (ρ + 1) u').comp continuous_fst).mul continuous_snd).measurable
  have hs := (MeasurePreserving.id m).skew_product hm2 (Filter.Eventually.of_forall fun g => map_mul_left_eq_self V _)
  exact hs.prod (MeasurePreserving.id _)

theorem mp_embX (ρ : ℕ) (ν : Measure k) [ν.IsAddHaarMeasure] (V : Measure (N k n c (ρ + 1))) [SFinite V]
    (m : Measure (GL n k)) [m.IsMulLeftInvariant] [SFinite m] (g' : GL n k) :
    MeasurePreserving (fun q : (GL n k × N k n c (ρ + 1)) × (n → k) => ((g' * q.1.1, q.1.2), q.2))
      ((m.prod V).prod (Measure.pi fun _ : n => ν)) ((m.prod V).prod (Measure.pi fun _ : n => ν)) :=
  ((measurePreserving_mul_left m g').prod (MeasurePreserving.id V)).prod (MeasurePreserving.id _)

end Kinds

theorem isMulLeftInvariant_map_prodRFJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), 1 ≤ ρ → ρ < c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → (((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)).map (prodRFJ ρ)).IsMulLeftInvariant := by
  intro k _ _ _ _ _ _ n _ _ c ρ h1 h2 ν hν m hm
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : BorelSpace (GL n k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  haveI : SecondCountableTopology (GL n k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : SecondCountableTopology (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : LocallyCompactSpace (GL n k) := GlobalTheory.SplitFlip.locallyCompact_GL
  haveI hVH : (volN ν n c (ρ + 1)).IsHaarMeasure :=
    (GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c (ρ + 1) (by omega) (by omega) ν).2.2.1
  haveI : SFinite (volN ν n c (ρ + 1)) := by rw [GlobalTheory.RootEx.VolN.volN_eq]; infer_instance
  have hf : Measurable (prodRFJ (k := k) (n := n) (c := c) ρ) := (continuous_prodRFJ ρ).measurable
  refine ⟨fun h => ?_⟩
  obtain ⟨r, hr, β', he⟩ := ((FourierJacobiGroup.mem_RFJ_iff k n c ρ h1 h2).1 h.1).1 h.2
  obtain ⟨g', u', hu', rfl⟩ := Radical.exists_of_mem_R hr
  have hg : embX c g' ∈ RFJ k n c ρ := Subgroup.mem_sup_right (Subgroup.mem_sup_left ⟨g', rfl⟩)
  have hu : u' ∈ RFJ k n c ρ := Subgroup.mem_sup_right (Subgroup.mem_sup_right hu')
  have hb : colE c (ρ + 1) β' ∈ RFJ k n c ρ := Subgroup.mem_sup_left (Subgroup.mem_sup_right
    ((GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c ρ).2.2.2.2.2.2.2 (ρ + 1) β' (Nat.lt_succ_self ρ)).1)
  have hh : h = (⟨embX c g', hg⟩ : RFJ k n c ρ) * ⟨u', hu⟩ * ⟨colE c (ρ + 1) β', hb⟩ := Subtype.ext he
  rw [hh]
  refine map_mul_left_mul _ _ _ (map_mul_left_mul _ _ _ ?_ ?_) ?_
  · exact map_mul_left_of_conj _ _ hf _ _ (mp_embX ρ ν _ m g') fun q => Subtype.ext (mul_prodRFJ_embX ρ g' q)
  · exact map_mul_left_of_conj _ _ hf _ _ (mp_N ρ ν _ m ⟨u', hu'⟩) fun q => Subtype.ext (mul_prodRFJ_N ρ ⟨u', hu'⟩ q)
  · exact map_mul_left_of_conj _ _ hf _ _ (mp_colE ρ h1 h2 ν m β') fun q => Subtype.ext (mul_prodRFJ_colE ρ h1 h2 β' q)

end GlobalTheory.HaarR.LeftFJ
end
end

