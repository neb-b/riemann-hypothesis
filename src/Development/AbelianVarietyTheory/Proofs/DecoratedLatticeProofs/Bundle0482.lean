module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0446
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineHomAdjointTwistMemCompletedHomLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0374
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineProjectionMemSplitCoreCompletion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LineProj

variable {D : D7}

theorem latV_le_of {S : HSp D} (L : Lat S) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) :
    GlobalTheory.FinPl.latV S L P ≤ GlobalTheory.FinPl.latV S L P' := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
  refine AddSubgroup.closure_mono ?_
  rintro y ⟨α, hα, hP, a, ha, x, hx, rfl⟩
  exact ⟨α, hα, fun v hv => hP v fun h' => hv (h v h'), a, ha, x, hx, rfl⟩

theorem row_iA {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    star (vecB o ζ) ᵥ* HSpace.gram S₀ ᵥ* o.iA = 0 := by
  show star (o.iB *ᵥ ζ) ᵥ* HSpace.gram S₀ ᵥ* o.iA = 0
  rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, o.orth,
    Matrix.vecMul_zero]

theorem row_vecB {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    (star (vecB o ζ) ᵥ* HSpace.gram S₀) ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  show (star (o.iB *ᵥ ζ) ᵥ* HSpace.gram S₀) ⬝ᵥ (o.iB *ᵥ ζ) = _
  rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, o.isoB]

theorem star_self {L : HSp D} (ζ : Fin L.rank → D.host.E) :
    star (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ) = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  conv_rhs => rw [Matrix.star_dotProduct, Matrix.star_mulVec, gram_conjTranspose, ← Matrix.dotProduct_mulVec]

theorem sum_incA_mulVec {s t : ℕ} (ρ : Fin s → D.host.E) (N : Matrix (Fin s) (Fin t) D.host.E) (u : Fin t → AE D) :
    ∑ j, incA D (ρ j) * (rat N *ᵥ u) j = ∑ a, incA D ((ρ ᵥ* N) a) * u a := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rat, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.map_apply, Finset.mul_sum, map_sum, map_mul,
    Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end GlobalTheory.LineProj

namespace GlobalTheory.LineProj

variable {D : D7}

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {q : SplitPt D k}
  {n : Type} [Fintype n] [DecidableEq n] {S₀ A L : HSp D} {o : OrthDec S₀ A L} {ζ : Fin L.rank → D.host.E}
  {α : Frame q A n} {α₀ : Frame q S₀ (n ⊕ Fin 1)} {M : Lat S₀} {Λ : Submodule 𝒪[k] (n → k)}

theorem e_vecB_mem (hsum : IsSumFrame o ζ α α₀) (hlat : α₀.IsLat M (lastKer Λ)) :
    (fun r => q.e * incA D (vecB o ζ r)) ∈ GlobalTheory.FinPl.latV S₀ M (· = q.v) := by
  let y0 : n ⊕ Fin 1 → k := Sum.elim 0 (fun _ => 1)
  have hb0 : α₀.b *ᵥ y0 = fun r => q.pr (incA D (vecB o ζ r)) := by
    rw [hsum, Matrix.fromCols_mulVec]
    funext r
    have h1 : y0 ∘ Sum.inl = 0 := Sum.elim_comp_inl _ _
    rw [Pi.add_apply, h1, Matrix.mulVec_zero, Pi.zero_apply, zero_add]
    simp only [Matrix.mulVec, dotProduct, Matrix.replicateCol_apply, Fin.sum_univ_one, Function.comp_apply, y0,
      Sum.elim_inr, mul_one]
    rfl
  have hy0 : y0 ∈ lastKer Λ := by
    refine GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨?_, ?_⟩
    · show (Sum.elim 0 (fun _ => 1) : n ⊕ Fin 1 → k) ∘ Sum.inl ∈ Λ
      rw [Sum.elim_comp_inl]; exact zero_mem _
    · exact one_mem _
  have h := (hlat y0).1 hy0
  rw [hb0] at h
  simpa only [q.sec_pr] using h

theorem pr_coeff_mem (hsum : IsSumFrame o ζ α α₀) (hlat : α₀.IsLat M (lastKer Λ)) {m : Fin S₀.rank → AE D} {c : AE D}
    (hmdec : ∀ r, m r = (o.jA *ᵥ (o.pA *ᵥ m)) r + c * incA D (vecB o ζ r))
    (hem : (fun r => q.e * m r) ∈ GlobalTheory.FinPl.latV S₀ M (· = q.v)) : q.pr c ∈ 𝒪[k] := by
  let pu : Fin A.rank → k := fun a => q.pr ((o.pA *ᵥ m) a)
  let y : n ⊕ Fin 1 → k := Sum.elim (α.b' *ᵥ pu) (fun _ => q.pr c)
  have hbx : α₀.b *ᵥ y = fun r => q.pr (m r) := by
    rw [hsum, Matrix.fromCols_mulVec]
    have h1 : (o.jA.map q.pr * α.b) *ᵥ (y ∘ Sum.inl) = o.jA.map q.pr *ᵥ pu := by
      show (o.jA.map q.pr * α.b) *ᵥ (α.b' *ᵥ pu) = _
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, α.bb', Matrix.mul_one]
    rw [h1]
    funext r
    rw [hmdec r, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mulVec, Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.replicateCol_apply, Fin.sum_univ_one, Function.comp_apply, y,
      Sum.elim_inr]
    exact mul_comm _ _
  have hy : y ∈ lastKer Λ := by
    refine (hlat y).2 ?_
    rw [hbx]
    simpa only [q.sec_pr] using hem
  exact (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy).2

theorem pr_cA_mem {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : q.pr (cA D a) ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, RingHom.map_mul]
  exact FrameLat.mul_mem_intAE (GlobalTheory.UpMem.finPart_e_int q) ((FrameLat.cA_int_iff a).2 ha.2)

theorem e_mul_mem (hM : IsSelfDualC S₀ M) {P : Pl D → Prop} {m : Fin S₀.rank → AE D}
    (hm : m ∈ GlobalTheory.FinPl.latV S₀ M P) : (fun r => q.e * m r) ∈ GlobalTheory.FinPl.latV S₀ M (· = q.v) := by
  refine FrameLat.mem_of_pairing hM (fun r => Ideal.mul_mem_right _ _ (FrameLat.e_mem_idAt q)) fun s hs => ?_
  have h : FrameLat.pairing S₀ s (fun r => q.e * m r) = q.e * FrameLat.pairing S₀ s m := by
    simp only [FrameLat.pairing, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h, RingHom.map_mul]
  exact FrameLat.mul_mem_intAE (GlobalTheory.UpMem.finPart_e_int q) (FrameLat.pairing_int hM hs hm)

end Local

theorem pairing_eq {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (e c : AE D)
    {m : Fin S₀.rank → AE D} (hmdec : ∀ r, m r = (o.jA *ᵥ (o.pA *ᵥ m)) r + c * incA D (vecB o ζ r)) :
    (∑ a, ∑ b, cA D (e * incA D (vecB o ζ a)) * incA D (HSpace.gram S₀ a b) * m b) =
      cA D e * (c * incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) ⬝ᵥ vecB o ζ)) := by
  have h1 : (∑ a, ∑ b, cA D (e * incA D (vecB o ζ a)) * incA D (HSpace.gram S₀ a b) * m b) =
      cA D e * ∑ b, incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * m b := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [RingHom.map_mul, FrameLat.cA_incA, Matrix.vecMul, dotProduct, map_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.star_apply]; ring
  rw [h1]
  congr 1
  have h2 : ∀ b, incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * m b =
      incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * (o.jA *ᵥ (o.pA *ᵥ m)) b +
        c * (incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * incA D (vecB o ζ b)) := fun b => by
    rw [hmdec b]; ring
  simp only [h2, Finset.sum_add_distrib]
  rw [OrthDec.jA, sum_incA_mulVec, row_iA]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, zero_add, ← Finset.mul_sum, ← RingHom.map_mul,
    ← map_sum]
  rfl

end GlobalTheory.LineProj

namespace GlobalTheory.LineProj


set_option maxHeartbeats 1000000 in
theorem lineProj_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ m ∈ latV S₀ M P, o.jB *ᵥ (o.pB *ᵥ m) ∈ latV S₀ M P := by
  intro D k _ _ _ _ ι p I P hP n _ _ S₀ A L o ζ hζ α α₀ M Λ hM hfr m hm
  have hr : L.rank = 1 := hζ.1
  let i0 : Fin L.rank := ⟨0, by omega⟩
  have hsub : ∀ j : Fin L.rank, j = i0 := fun j => Fin.ext (by have := j.2; simp only [i0]; omega)
  have hz0 : ζ i0 ≠ 0 := by
    intro h0
    apply hζ.2
    have : ζ = 0 := funext fun j => by rw [hsub j, h0]; rfl
    rw [this]; simp
  have hmid : ∀ r, m r ∈ idAt D P := FrameLat.latV_supp hm
  set c : AE D := (o.pB *ᵥ m) i0 * incA D (ζ i0)⁻¹ with hc
  have hcid : c ∈ idAt D P := by
    refine Ideal.mul_mem_right _ _ ?_
    show (∑ j, o.pB i0 j * m j) ∈ idAt D P
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hmid j)
  have hpB : o.pB *ᵥ m = fun j => c * incA D (ζ j) := by
    funext j
    rw [hsub j, hc, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hz0, RingHom.map_one, mul_one]
  have hjB : o.jB *ᵥ (o.pB *ᵥ m) = fun r => c * incA D (vecB o ζ r) := by
    rw [hpB]; funext r
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, OrthDec.jB, rat, Matrix.map_apply, vecB, map_sum, RingHom.map_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmdec : ∀ r, m r = (o.jA *ᵥ (o.pA *ᵥ m)) r + c * incA D (vecB o ζ r) := by
    intro r
    have h : m = o.jA *ᵥ (o.pA *ᵥ m) + o.jB *ᵥ (o.pB *ᵥ m) := by
      have hs : o.jA * o.pA + o.jB * o.pB = 1 := by
        rw [OrthDec.jA, OrthDec.jB, OrthDec.pA, OrthDec.pB, rat, rat, rat, rat,
          ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add (incA D)),
          o.iA_qA_add, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hs, Matrix.one_mulVec]
    conv_lhs => rw [h]
    rw [Pi.add_apply, hjB]
  rw [hjB]
  refine (_root_.GlobalTheory.LineIdeal.mem_latV_iff D k ι p I P hP n S₀ A L o ζ hζ α α₀ M Λ hM hfr c hcid).2 fun i => ?_
  obtain ⟨hsum, hlat⟩ := hfr i
  have hvP : P (p i).v := (hP.mem _).2 ⟨i, rfl⟩
  have hpre : (p i).pr (p i).e = 1 := by rw [← FrameLat.sec_one, (p i).pr_sec]
  refine ⟨pr_coeff_mem hsum hlat hmdec (e_mul_mem hM hm), ?_⟩
  have hzP := latV_le_of M (P := (· = (p i).v)) (P' := P) (fun w hw => by rw [hw]; exact hvP) (e_vecB_mem hsum hlat)
  have hH := (_root_.GlobalTheory.FinPl.SelfDualCompl.selfDual_latV D S₀ M hM P m hmid).1 hm _ hzP
  have h := pr_cA_mem (q := p i) hH
  rw [pairing_eq o ζ (p i).e c hmdec, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, cA_cA, hpre, one_mul,
    FrameLat.cA_incA, row_vecB, star_self, RingHom.map_mul] at h
  exact h

end GlobalTheory.LineProj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitAtPlaces

theorem splitAt_places : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), SplitAt { v with N := N₁ } { o with M := M₁ } ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hz hvτ hNT hoζ hsdT hgP htP hdisj hpre hLZ hbas FY sc hFY N₁ M₁ hN₁ hFYN hM₁ hcore PP hP
  have hq : (l PP hP).q.v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := (l PP hP).under
  obtain ⟨hsc, hstep, hhz, -, -, hτ⟩ := hFY PP hP
  have hξ : valuation (l PP hP).k (ofSplit (l PP hP).q).xi = 1 := by
    have h1 := hsc (0 + 1 + 1)
    rw [hstep 0, map_mul, hsc 0, one_mul] at h1
    exact h1
  have hxi : (ofSplit (l PP hP).q).xi ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hξ
    exact zero_ne_one hξ

  have key : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), ∃ LL : GlobalTheory.FinPl.Lat (y.bes j ρ h).L, IsSelfDualC _ LL ∧
      GlobalTheory.FinPl.OrthAt (y.bes j ρ h).o (M₁ j ρ h) (a.x j).L LL (l PP hP).q.v ∧
      ∀ t : (l PP hP).k, (t ∈ 𝒪[(l PP hP).k] ↔ (fun i => (l PP hP).q.sec
        ((fun i => sc PP hP j * (ofSplit (l PP hP).q).pr ((y.bes j ρ h).ζ i)) i * t)) ∈ GlobalTheory.FinPl.latV _ LL (· = (l PP hP).q.v)) := by
    intro j ρ h
    have hj : j ≤ (l PP hP).s + 1 := by have := (l PP hP).hs; omega
    have hs0 : sc PP hP j ≠ 0 := by
      intro h0
      have h1 := hsc j
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    obtain ⟨F₀, hF₀⟩ := ((_root_.GlobalTheory.LocMod.normalFrames_and_basePoint_exist D (l PP hP).k (ofSplit (l PP hP).q) hxi).1 _ ρ ((y.bes j ρ h).lev (a.x j).vol)
      (sc PP hP j) ((l PP hP).FX j hj) hs0).1
    have hIntM := hcore PP hP j ρ h hj F₀ hF₀
    have hA : IsSelfDualC (D.sp.X j) (a.x j).L := (hIs.x j (by omega)).sd
    refine _root_.GlobalTheory.LineSplit.exists_lineLat D (l PP hP).k (l PP hP).q (y.bes j ρ h).V₀ (D.sp.X j) (y.bes j ρ h).L (y.bes j ρ h).o (M₁ j ρ h)
      (a.x j).L _ ((l PP hP).FX j hj) F₀ _ (hM₁ j ρ h) hA ⟨_, GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D _⟩ hF₀.1 (fun r => ?_)
      hIntM ((l PP hP).latX j hj)
    rw [hF₀.2 r]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.MixPer.vecB, Matrix.mulVec, dotProduct, Matrix.map_apply, GlobalTheory.LocMod.Place.pr, map_sum, map_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hx : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ v.tP := by
    rcases hP with hP' | hP'
    · intro ht
      exact Finset.disjoint_left.1 hdisj ((hgP _).2 ⟨PP, hP', rfl⟩) ht
    · exact GlobalTheory.tuplePlace_under_not_mem_tP W u hW a y m b₀ k ι v o l bas hIs hTau hz hvτ hNT hoζ hsdT hgP htP hdisj hpre hLZ
        hbas FY sc hFY PP hP'
  refine ⟨fun j ρ h => ?_, fun j h => ?_⟩
  · obtain ⟨LL, hLL, hO, -⟩ := key j ρ h
    exact ⟨LL, hLL, hq ▸ hO⟩
  · have hjs : j = (l PP hP).s := by have := (l PP hP).hs; omega
    subst hjs
    obtain ⟨LL, hLL, hO, hLLw⟩ := key _ 0 h
    obtain ⟨LZ₀, hLZ₀, -⟩ := hLZ _ h (l PP hP).q.v (hq ▸ hx)
    obtain ⟨LZ, hLZsd, hLZO, hLZw⟩ := _root_.GlobalTheory.LineSplit.exists_lineLat D (l PP hP).k (l PP hP).q (D.sp.X ((l PP hP).s + 1 + 1)) D.sp.X' a.Lz
      (a.oT _ h) (a.x ((l PP hP).s + 1 + 1)).L a.LT _ (l PP hP).FT (l PP hP).FM
      (fun i => (ofSplit (l PP hP).q).pr (a.ζ₀ i)) (hIs.x _ (by omega)).sd hsdT ⟨LZ₀, hLZ₀⟩
      (fun r b => by rw [(l PP hP).last]; rfl) (fun r => by rw [(l PP hP).last]; rfl) (l PP hP).latM (l PP hP).latT
    refine ⟨LL, LZ, hLL, hLZsd, hq ▸ hO, hNT ▸ hq ▸ hLZO, ?_⟩
    intro w hw
    rw [← hq] at hw ⊢
    rw [hvτ]
    have hmap := _root_.GlobalTheory.SplitLineSim.line_sim_maps D (l PP hP).k (l PP hP).q (y.bes _ 0 h).L a.Lz (y.τ _ h) LL LZ _ _ (-(ofSplit (l PP hP).q).xi)
      (l PP hP).unit hLL hLZsd (y.bes _ 0 h).line.1 hpre.line.1 hLLw hLZw (by rw [Valuation.map_neg]; exact hξ)
      (by rw [hτ h]; funext i; simp only [Pi.smul_apply, smul_eq_mul]; ring) (hTau _ h).1
    exact _root_.GlobalTheory.KapLat2.kap_mem_latO D (l PP hP).k (l PP hP).q (D.sp.X ((l PP hP).s + 1)) (y.bes _ 0 h).L a.Lz (y.τ _ h)
      (a.x ((l PP hP).s + 1)).L LL LZ (l PP hP).unit (hIs.x _ (by omega)).sd hLL hLZsd hmap w hw

end GlobalTheory.SplitAtPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLineHomLatticeCompletionIffScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Corev.mem_latO_line_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n'' : Type) [Fintype n''] [DecidableEq n''] (σ : ℕ) (B' : BesLev D σ) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M' : Lat B'.V₀) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ (∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ)) ∈ 𝒪[k])) := by
  intro D k _ _ _ _ ι p I P hP n'' _ _ σ B' γ γ₀ M' Λ' hM' hγ S LS hLS x hx
  have hu : (B'.o.resT S).symm (0, x) = B'.o.jB ⬝ x := by
    rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
  have hMx : MxAt P (B'.o.jB ⬝ x) := by
    intro i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)
  obtain ⟨hrk, hne⟩ := B'.line
  have hr : ∀ r r' : Fin B'.L.rank, r = r' := fun r r' => Fin.ext (by omega)
  let r₀ : Fin B'.L.rank := ⟨0, by omega⟩
  have hζ : B'.ζ r₀ ≠ 0 := by
    intro h0
    apply hne
    have : B'.ζ = 0 := funext fun r => by rw [hr r r₀, h0]; rfl
    rw [this, Matrix.mulVec_zero, dotProduct_zero]
  have hjB : ∀ d : AE D, B'.o.jB *ᵥ (d • ratV B'.ζ) = fun r => d * incA D (vecB B'.o B'.ζ r) := by
    intro d
    funext r
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, OrthDec.jB, rat, Matrix.map_apply, ratV, Pi.smul_apply, smul_eq_mul, vecB,
      map_sum, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have key : ∀ y, (B'.o.jB ⬝ x) *ᵥ y ∈ latV B'.V₀ M' P ↔ ∃ d : AE D, d ∈ idAt D P ∧
      (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ (∀ i, (p i).pr d ∈ 𝒪[k] ∧
        (p i).pr (cA D d) * (p i).pr (incA D (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ)) ∈ 𝒪[k]) := by
    intro y
    rw [← Matrix.mulVec_mulVec]
    constructor
    · intro h
      have hz : ((x : Matrix _ _ (AE D)) *ᵥ y) r₀ ∈ idAt D P := by
        simp only [Matrix.mulVec, dotProduct]
        exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hx r₀ j)
      set d : AE D := ((x : Matrix _ _ (AE D)) *ᵥ y) r₀ * incA D (B'.ζ r₀)⁻¹ with hd
      have hdI : d ∈ idAt D P := Ideal.mul_mem_right _ _ hz
      have hzd : (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ := by
        funext r
        rw [hr r r₀, Pi.smul_apply, smul_eq_mul, ratV, hd, mul_assoc, ← map_mul, inv_mul_cancel₀ hζ, map_one, mul_one]
      rw [hzd, hjB] at h
      exact ⟨d, hdI, hzd, (_root_.GlobalTheory.LineIdeal.mem_latV_iff D k ι p I P hP n'' B'.V₀ B'.A B'.L B'.o B'.ζ B'.line γ γ₀ M' Λ' hM' hγ d hdI).1 h⟩
    · rintro ⟨d, hdI, hzd, hc⟩
      rw [hzd, hjB]
      exact (_root_.GlobalTheory.LineIdeal.mem_latV_iff D k ι p I P hP n'' B'.V₀ B'.A B'.L B'.o B'.ζ B'.line γ γ₀ M' Λ' hM' hγ d hdI).2 hc
  rw [hu, _root_.GlobalTheory.FinPl.LatMem.mem_latO_iff D S B'.V₀ LS M' hLS hM' P, _root_.GlobalTheory.FinPl.UnitPlaces.latA_eq_latV D k ι p I P hP B'.V₀ M']
  constructor
  · rintro ⟨-, h⟩ y hy
    exact (key y).1 (h y hy)
  · intro h
    exact ⟨hMx, fun y hy => (key y).2 (h y hy)⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiPrimitiveOfInverseDifferentLines
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.SeeSaw.AdaptFBIdeals

theorem primAt_lastAt_of_lines : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L : Lat S) (M : Lat S₀) (μ : D.host.E) (v : GlobalTheory.FinPl.Pl D), μ ≠ 0 → LineAt z μ M v → (∀ i : Fin ρ, ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ incA D μ * a ∈ idV (dI D ^ (ρ - i.1)) v) → PrimAt ψ d L v ∧ LastAt ψ d z L M v := by
  intro D ψ hψ S S₀ ρ d z L M μ v hμ hline hcol
  have hdI : dI D ≠ 0 := (GlobalTheory.SeeSaw.ChainIdeals.host_ne_zero D).2.2.2
  have hu : incA D μ⁻¹ * incA D μ = 1 := by rw [← map_mul, inv_mul_cancel₀ hμ, map_one]
  have key : ∀ 𝔞 𝔟 : FI D, 𝔞 ≠ 0 → 𝔟 ≠ 0 → 𝔟 * 𝔞⁻¹ = dI D → ∀ s ∈ idAt D (· = v),
      ((∀ a ∈ idAt D (· = v), incA D μ * a ∈ idV 𝔞 v → incA D μ * (s * a) ∈ idV 𝔟 v) ↔
        ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) := by
    intro 𝔞 𝔟 h𝔞 h𝔟 hq s hs
    rw [← GlobalTheory.SeeSaw.DiffDual.idV_dI_iff D ψ hψ v s hs, ← hq, ← _root_.GlobalTheory.IdealQuot.mul_subset_iff D v 𝔞 𝔟 h𝔞 h𝔟 s hs]
    constructor
    · intro h b hb
      have hbAt := idV_supp 𝔞 v hb
      have ha : incA D μ⁻¹ * b ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hbAt
      have hb' : incA D μ * (incA D μ⁻¹ * b) = b := by rw [← mul_assoc, mul_comm (incA D μ), hu, one_mul]
      have h2 := h _ ha (by rw [hb']; exact hb)
      rwa [mul_left_comm, hb'] at h2
    · intro h a _ hma
      rw [mul_left_comm]
      exact h _ hma
  constructor
  · intro i j hij s hs
    have hq : dI D ^ (ρ - i.1) * (dI D ^ (ρ - j.1))⁻¹ = dI D := by
      have he : ρ - i.1 = (ρ - j.1) + 1 := by have := j.2; omega
      rw [he, pow_succ, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hdI), one_mul]
    rw [← key (dI D ^ (ρ - j.1)) (dI D ^ (ρ - i.1)) (pow_ne_zero _ hdI) (pow_ne_zero _ hdI) hq s hs]
    constructor
    · intro h a ha hma
      exact (hcol i (s * a) (Ideal.mul_mem_left _ _ ha)).1 (h a ((hcol j a ha).2 hma))
    · intro h a ha
      have haAt := supp_of_colMul d L v j a ha
      exact (hcol i (s * a) (Ideal.mul_mem_left _ _ haAt)).2 (h a haAt ((hcol j a haAt).1 ha))
  · intro i hi s hs
    rw [← key 1 (dI D) one_ne_zero hdI (by rw [inv_one, mul_one]) s hs]
    have hρi : ρ - i.1 = 1 := by omega
    constructor
    · intro h a ha hma
      rw [GlobalTheory.SeeSaw.idV_one_eq_intAt] at hma
      have h2 := (hcol i (s * a) (Ideal.mul_mem_left _ _ ha)).1 (h a ha ((hline a ha).2 hma))
      rwa [hρi, pow_one] at h2
    · intro h a ha hz
      have h2 := h a ha ((GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).2 ((hline a ha).1 hz))
      exact (hcol i (s * a) (Ideal.mul_mem_left _ _ ha)).2 (by rwa [hρi, pow_one])

end GlobalTheory.Core.Mi.LatMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroRamifiedFormsTransportIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZero_ramifiedForms_transport_iff : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), I.Law0 l → ∀ (u : B.Word) (a : I.ι) (ψ₀ : ((I.rec7 l Z).mem u).C.cls 0 → ((I.rec7 l Z).mem u).C.Y 0 → ℂ), ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram ↔ GlobalTheory.AdForm.RamT (I := I) (l := l) (u := u) (a := a) 0 ((I.rec7 l Z).e0Tw u a ψ₀) := by
  first | exact @GlobalTheory.RamZero.mram_iff_ramT | exact GlobalTheory.RamZero.mram_iff_ramT | (intros; apply GlobalTheory.RamZero.mram_iff_ramT <;> assumption)
end

