module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

theorem ratV_vecB {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) :
    ratV (vecB o ζ) = o.jB *ᵥ ratV ζ :=
  funext fun i => RingHom.map_mulVec (incA D) o.iB ζ i

theorem mt_one' (S : HSp D) : Formalism.L2.Theta.mt S 1 = 1 := GlobalTheory.FinPlLoc.mt_one S

theorem emb_mem_grpAt {S A B : HSp D} (o : OrthDec S A B) {P : GlobalTheory.FinPl.Pl D → Prop} {a : GA D A} (ha : a ∈ grpAt A P) :
    o.emb (a, 1) ∈ grpAt S P := by
  have ha' := (GlobalTheory.IwaPlace.mem_congGrp_iff A (idAt D P) a).1 ha
  refine (GlobalTheory.IwaPlace.mem_congGrp_iff S (idAt D P) _).2 fun i j => ?_
  have e : Formalism.L2.Theta.mt S (o.emb (a, 1)) - 1 = HMul.hMul (HMul.hMul o.jA (Formalism.L2.Theta.mt A a - 1)) o.pA := by
    rw [o.mt_emb, ← o.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, mt_one', Matrix.mul_one, Matrix.mul_one]
    abel
  rw [← Matrix.sub_apply, e, Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (by rw [Matrix.sub_apply]; exact ha' l k)

theorem embA_mem_grpAt {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {P : GlobalTheory.FinPl.Pl D → Prop}
    {a : GA D A} (ha : a ∈ grpAt A P) : embA d o a ∈ grpAt S P :=
  GlobalTheory.IwaPlace.wittCoreEmbedding_preserves_supportedUnitarySubgroup d (emb_mem_grpAt o ha)

theorem emb_fix {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (a : GA D A) :
    Formalism.L2.Theta.mt S (o.emb (a, 1)) *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
  rw [ratV_vecB, Matrix.mulVec_mulVec]
  have := o.emb_jB a 1
  rw [mt_one', Matrix.mul_one] at this
  exact congrArg (· *ᵥ ratV ζ) this

theorem j_zero_mul_mem_lattice_iff {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (M : Lat S₀) (v : GlobalTheory.FinPl.Pl D)
    (hL : MonoAt d L M v) (w : Fin S₀.rank → AE D) : d.j0 *ᵥ w ∈ latV S L (· = v) ↔ w ∈ latV S₀ M (· = v) := by
  have hc : ∀ {n : ℕ} (x : Mx D S.rank n) (i : Fin n), colMul x i 0 = 0 := fun x i => by
    funext k; simp [colMul]
  rw [hL]
  simp only [Matrix.mulVec_mulVec, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.zero_mulVec, Matrix.one_mulVec, Pi.zero_apply, hc,
    zero_mem, implies_true, true_and]

theorem line_loc {S : HSp D} {L : Lat S} {x : Fin S.rank → D.host.E} (hL : IsSelfDualC S L) (hx : x ≠ 0) {c : D.host.E}
    (hc : c ≠ 0) {𝔟 : FI D} (h : ∀ t : D.host.E, t • x ∈ L ↔ c * t ∈ 𝔟) (v : GlobalTheory.FinPl.Pl D) :
    ∀ a ∈ idAt D (· = v), a • ratV x ∈ latV S L (· = v) ↔ incA D c * a ∈ idV 𝔟 v := by
  obtain ⟨𝔞, -, h1, h2⟩ := _root_.GlobalTheory.Core.Mi.LatLine.line_trace D S L x hL hx
  have e : 𝔞 = FractionalIdeal.spanSingleton _ c⁻¹ * 𝔟 := by
    ext t
    rw [← h1, h, FractionalIdeal.mem_singleton_mul]
    constructor
    · intro ht
      exact ⟨c * t, ht, by field_simp⟩
    · rintro ⟨y, hy, rfl⟩
      rwa [mul_inv_cancel_left₀ hc]
  intro a ha
  rw [h2 v a ha, e, GlobalTheory.SeeSaw.idV_spanSingleton_mul_iff D v 𝔟 c⁻¹ (inv_ne_zero hc), inv_inv]
  exact and_iff_left ha

theorem col_e_ne {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) : (fun r => d.e r i) ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun d.e'e i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have : ∀ r, d.e r i = 0 := fun r => congrFun h r
  simp [this] at h1

theorem col_e'_ne {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) : (fun r => d.e' r i) ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun d.e'e i) i
  rw [Matrix.mul_assoc, Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have : ∀ r, d.e' r i = 0 := fun r => congrFun h r
  simp [this] at h1

theorem nat_mul_mem_iff {N : ℕ} {v : GlobalTheory.FinPl.Pl D} (hN : (N : 𝓞 D.host.F) ∉ v.asIdeal) (𝔟 : FI D) (a : AE D) :
    incA D (N : D.host.E) * a ∈ idV 𝔟 v ↔ a ∈ idV 𝔟 v := by
  have h0 : (N : D.host.E) ≠ 0 := by
    intro h
    have : N = 0 := by exact_mod_cast h
    exact hN (by rw [this, Nat.cast_zero]; exact zero_mem _)
  constructor
  · intro h
    have := GlobalTheory.SeeSaw.idV_natInv_mul_le D 𝔟 N v hN (GlobalTheory.SeeSaw.idV_incA_mul ((N : D.host.E)⁻¹) 𝔟 v h)
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul] at this
  · intro h
    rw [map_natCast, ← nsmul_eq_mul]
    exact nsmul_mem h N

theorem pow_mul_mem_iff {N : ℕ} {v : GlobalTheory.FinPl.Pl D} (hN : (N : 𝓞 D.host.F) ∉ v.asIdeal) {lam : D.host.E}
    (hl : lam = (N : D.host.E) ∨ lam = -(N : D.host.E)) (𝔟 : FI D) (n : ℕ) (a : AE D) :
    incA D (lam ^ n) * a ∈ idV 𝔟 v ↔ a ∈ idV 𝔟 v := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, map_mul, mul_assoc, ih]
    rcases hl with rfl | rfl
    · exact nat_mul_mem_iff hN 𝔟 a
    · rw [map_neg, neg_mul, neg_mem_iff]; exact nat_mul_mem_iff hN 𝔟 a

theorem val_nat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    {N : ℕ} (hN : (N : 𝓞 D.host.F) ∉ p.v.asIdeal) : valuation k (p.pr (incA D (N : D.host.E))) = 1 := by
  obtain ⟨PP, hP⟩ := GlobalTheory.SeeSaw.LevelTest.exists_prime p
  obtain ⟨ε, hε, he⟩ := p.above
  have hu := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP _ ε hP hε he
  have h1 := GlobalTheory.SeeSaw.LevelTest.val_le_one p (N : 𝓞 D.host.E)
  have h2 := GlobalTheory.SeeSaw.LevelTest.val_lt_one_iff p hP (N : 𝓞 D.host.E)
  have e : ((N : 𝓞 D.host.E) : D.host.E) = N := by simp
  rw [e] at h1 h2
  refine le_antisymm h1 (not_lt.1 fun h => hN ?_)
  rw [← hu]
  have := h2.1 h
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (N : 𝓞 D.host.F) ∈ PP.asIdeal
  rwa [map_natCast]

section Rows

variable {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (AF D.host.F) ℂ} {B : SBes X h u ψ (D.sp.X 0)} {μ lam : D.host.E}

theorem g_ne (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : ((X.B.g : ℕ) : D.host.E) ≠ 0 := by
  rw [X.g_eq]
  exact Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)

theorem lam_ne (hF : B.FrameAt μ lam) : lam ≠ 0 := by
  rcases hF.sign with hl | hl <;> rw [hl]
  · exact g_ne X
  · exact neg_ne_zero.2 (g_ne X)

theorem scl_ne (hF : B.FrameAt μ lam) (i : Fin D.R.rS) : GlobalTheory.Core.SBesEx.scl μ lam i ≠ 0 :=
  mul_ne_zero hF.ne (pow_ne_zero _ (lam_ne hF))

theorem rows_shape (hE : GlobalTheory.Core.Mi.IdE X) (hF : B.FrameAt μ lam) :
    IsSelfDualC (D.sp.Y 0) (latS D) ∧ IsSelfDualC B.V₀ (coreLat B.d (latS D)) ∧
    (∀ v, MonoAt B.d (latS D) (coreLat B.d (latS D)) v) ∧
    (∀ v (i : Fin D.R.rS), ∀ a ∈ idAt D (· = v), colMul B.d.jX i a ∈ latV (D.sp.Y 0) (latS D) (· = v) ↔
      incA D (GlobalTheory.Core.SBesEx.scl μ lam i) * a ∈ idV (dI D ^ (D.R.rS - i.1)) v) ∧
    (∀ v (i : Fin D.R.rS), ∀ a ∈ idAt D (· = v), colMul B.d.jY i a ∈ latV (D.sp.Y 0) (latS D) (· = v) ↔
      incA D (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ * a ∈ idV (dI D ^ (D.R.rS - i.1))⁻¹ v) ∧
    ∀ v, LineAt (vecB B.o B.ζ) μ (coreLat B.d (latS D)) v := by
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.Core.Mi.LatMatch.latS_rescaled_frame D X h u ψ _ B μ lam hE hF
  obtain ⟨h5, h6⟩ := GlobalTheory.T.selfDual_lineStable_lattice_splitsAlongWitt_selfDualCore D _ _ _ B.d (latS D) h1 h2
  obtain ⟨h7, -, h8⟩ := _root_.GlobalTheory.Core.Mi.LatMatch.sz_tied D X h u ψ _ B μ lam hE hF
  refine ⟨h1, h5, h6, fun v i => ?_, fun v i => ?_, fun v a ha => ?_⟩
  · rw [← _root_.GlobalTheory.Core.Mi.LatMatch.DiffInv.aaD_eq_dI_pow D i]
    exact line_loc h1 (col_e_ne B.d i) (scl_ne hF i) (h3 i) v
  · rw [← _root_.GlobalTheory.Core.Mi.LatMatch.DiffInv.aaD_eq_dI_pow D i]
    exact line_loc h1 (col_e'_ne B.d i) (inv_ne_zero (star_ne_zero.2 (scl_ne hF i))) (h4 i) v
  · rw [line_loc h5 h8 hF.ne h7 v a ha, GlobalTheory.SeeSaw.idV_one_eq_intAt]

variable {F : Formalism.L2.Forms.Forms0 D u} {tr : Formalism.L2.SG.ColDict.Transport X u F} {hK : X.LevelSubgroupCharacter} {a₀ : GA D (D.sp.X 0)}

theorem rows_trace (hE : GlobalTheory.Core.Mi.IdE X) (hF : B.FrameAt μ lam) (hM : Formalism.L2.SG.ColDict.LevelMatch X tr hK)
    (hA : B.Adapted tr.wt) (h0 : IsTransportAdelicCorrection tr a₀) (v : GlobalTheory.FinPl.Pl D) {N : Lat (D.sp.X 0)}
    (hN : latV (D.sp.X 0) N (· = v) = latV (D.sp.X 0) (lat0 F) (· = v)) : TraceAt B.o a₀ N (coreLat B.d (latS D)) v := by
  intro y hy
  rw [hN, _root_.GlobalTheory.Core.Mi.LatMatch.TraceX.trace_iff D X h u ψ F tr hK B a₀ hE hM hA h0 v y hy, j_zero_mul_mem_lattice_iff B.d _ _ v ((rows_shape hE hF).2.2.1 v)]

theorem loc_of_core (hψ : IsStdChar D ψ (-1)) (hE : GlobalTheory.Core.Mi.IdE X) (hF : B.FrameAt μ lam) {v : GlobalTheory.FinPl.Pl D}
    (hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) {L : Lat (D.sp.Y 0)} {M : Lat B.V₀}
    (hL : IsSelfDualC (D.sp.Y 0) L) (hM : IsSelfDualC B.V₀ M) (h1 : MonoAt B.d L M v) (h2 : PrimAt ψ B.d L v)
    (h3 : LastAt ψ B.d (vecB B.o B.ζ) L M v)
    (hc : ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) v a ∧ NormOneAt v c ∧
      SMoves B.V₀ c (B.o.emb (a₀ * a, 1)) M (coreLat B.d (latS D)) v) :
    ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) v a ∧ NormOneAt v c ∧
      SMoves (D.sp.Y 0) c (embA B.d B.o (a₀ * a)) L (latS D) v := by
  obtain ⟨a, c, ha, hc, hm⟩ := hc
  obtain ⟨s1, s2, s3, s4, -, s6⟩ := rows_shape hE hF
  have hl : lam = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E) ∨ lam = -((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E) := by
    rw [← X.g_eq]; exact hF.sign
  obtain ⟨p1, p2⟩ := _root_.GlobalTheory.Core.Mi.LatMatch.primAt_lastAt_of_lines D ψ hψ _ _ _ B.d (vecB B.o B.ζ) (latS D) _ μ v hF.ne (s6 v) (fun i x hx => by
    rw [s4 v i x hx, GlobalTheory.Core.SBesEx.scl, mul_comm μ, map_mul, mul_assoc, pow_mul_mem_iff hg hl])
  exact ⟨a, c, ha, hc, _root_.GlobalTheory.Core.Mi.LatMatch.homothetic_of_monomial_primitive_selfDual_cores D ψ _ _ _ B.d (vecB B.o B.ζ) L (latS D) M _ v c _ hL s1 hM
    (_root_.GlobalTheory.Core.Mi.LatMatch.sz_tied D X h u ψ _ B μ lam hE hF).2.2 h1 (s3 v) h2 p1 h3 p2 hc (emb_fix _ _ _) hm⟩

theorem loc_level (hE : GlobalTheory.Core.Mi.IdE X) (hF : B.FrameAt μ lam) (hM : Formalism.L2.SG.ColDict.LevelMatch X tr hK)
    (hA : B.Adapted tr.wt) (h0 : IsTransportAdelicCorrection tr a₀) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (hp : p.UnitAA) (ϖ : k)
    (hϖ : valuation k (p.pr (incA D ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))) = valuation k ϖ)
    (hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ p.v.asIdeal)
    (hz : valuation k (p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ))) = 1) {L : Lat (D.sp.Y 0)} {N : Lat (D.sp.X 0)}
    (hL : IsSelfDualC (D.sp.Y 0) L) (hN : latV (D.sp.X 0) N (· = p.v) = latV (D.sp.X 0) (lat0 F) (· = p.v))
    (hW : WShape p B.d B.o B.ζ L (fun i => (ϖ ^ (i.1 + 1))⁻¹) (fun i => (ϖ ^ (2 * D.R.rS - i.1 + 1))⁻¹) ((ϖ ^ (D.R.rS + 1))⁻¹)
      1 N) :
    ∃ (a : GA D (D.sp.X 0)) (c : AE D), CenAt (D.sp.X 0) p.v a ∧ NormOneAt p.v c ∧
      SMoves (D.sp.Y 0) c (embA B.d B.o (a₀ * a)) L (latS D) p.v := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := rows_shape hE hF
  obtain ⟨-, z2, -⟩ := _root_.GlobalTheory.Core.Mi.LatMatch.sz_tied D X h u ψ _ B μ lam hE hF
  have hS := GlobalTheory.T.splitPlaceComponent_monomialLattice_splitCore D k p _ _ _ _ _ B.d B.o B.ζ (latS D) _ N (fun i => GlobalTheory.Core.SBesEx.scl μ lam i)
    (fun i => (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹) μ a₀ (s3 _)
    (fun i x hx => by rw [s4 _ i x hx, (_root_.GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit D k p hp _ _).1]) (fun i x hx => by rw [s5 _ i x hx, (_root_.GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit D k p hp _ _).2])
    (s6 _) (_root_.GlobalTheory.Core.Mi.LatMatch.SplitOff.splitsAt D _ _ _ B.o B.ζ _ μ _ _ B.line s2 hF.ne (s6 _) z2 hT) (rows_trace hE hF hM hA h0 _ hN)
  set f : D.host.E →+* k := p.pr.comp (incA D) with hf
  have hfe : ∀ x, p.pr (incA D x) = f x := fun _ => rfl
  have vg : valuation k (f lam) = valuation k ϖ := by
    rw [← hϖ, ← X.g_eq, hfe]
    rcases hF.sign with hl | hl <;> rw [hl]
    rw [map_neg, Valuation.map_neg]
  have vg' : valuation k (f (star lam)) = valuation k ϖ := by
    rw [← vg]
    rcases hF.sign with hl | hl <;> rw [hl] <;> simp
  have hϖ0 : valuation k ϖ ≠ 0 := by
    rw [← vg]; exact (Valuation.ne_zero_iff _).2 ((map_ne_zero f).2 (lam_ne hF))
  have hμ0 : valuation k (f μ) ≠ 0 := (Valuation.ne_zero_iff _).2 ((map_ne_zero f).2 hF.ne)
  have hμ : valuation k (f (star μ)) = (valuation k (f μ))⁻¹ := by
    have hT' := val_nat p hT
    rw [z2, hfe, map_neg, Valuation.map_neg, map_mul, map_mul, map_mul, map_mul, ← hfe (Nat.cast _), hT', mul_one] at hz
    exact eq_inv_of_mul_eq_one_right hz
  refine _root_.GlobalTheory.Core.Mi.LatMatch.sMoves_of_wShape D k p _ _ _ _ _ B.d B.o B.ζ L (latS D) N N _ _ _ _ _ _ (ϖ ^ (D.R.rS + 1) * f μ)⁻¹ a₀ B.line hL s1 hW hS rfl
    (inv_ne_zero (mul_ne_zero (pow_ne_zero _ ((Valuation.ne_zero_iff _).1 hϖ0)) ((map_ne_zero f).2 hF.ne))) (fun i => ?_)
    (fun i => ?_) ?_
  · have e : D.R.rS + 1 = (D.R.rS - i.1) + (i.1 + 1) := by have := i.2; omega
    simp only [hfe, GlobalTheory.Core.SBesEx.scl, map_mul, map_pow, map_inv₀, vg]
    rw [e, pow_add _ (D.R.rS - i.1)]
    field_simp
  · have e : 2 * D.R.rS - i.1 + 1 = (D.R.rS - i.1) + (D.R.rS + 1) := by have := i.2; omega
    simp only [hfe, GlobalTheory.Core.SBesEx.scl, star_mul', star_pow, map_mul, map_pow, map_inv₀, vg', hμ]
    rw [e, pow_add _ (D.R.rS - i.1)]
    field_simp
  · simp only [hfe, map_mul, map_pow, map_inv₀]
    field_simp

end Rows

theorem mem_GfC_of_grpAt {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {a : GA D S} (ha : a ∈ grpAt S P) : a ∈ GfC S := by
  rw [GlobalTheory.Core.Mi.CenAct.mem_GfC_iff]
  ext i j
  have h1 := GlobalTheory.FinPlLoc.infPart_of_idAt ((GlobalTheory.IwaPlace.mem_congGrp_iff S (idAt D P) a).1 ha i j)
  rw [RingHom.map_sub, sub_eq_zero] at h1
  rw [Matrix.map_apply]
  refine Eq.trans h1 ?_
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

theorem conj_mem_grpAt {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {a : GA D S} (ha : a ∈ grpAt S P) (t : GA D S) :
    t⁻¹ * a * t ∈ grpAt S P := by
  have := (MonoidHom.normal_ker _).conj_mem a ha t⁻¹
  rwa [inv_inv] at this

theorem moves_trans {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {g g' : GA D S} {L M N : Lat S} (h : Moves S g L M P)
    (h' : Moves S g' M N P) : Moves S (g' * g) L N P := by
  intro y hy
  rw [h y hy, h' _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy), Matrix.mulVec_mulVec, GlobalTheory.FinPlLoc.mt_mul]

theorem moves_symm {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D S} {L M : Lat S} (h : Moves S g L M P) :
    Moves S g⁻¹ M L P := by
  intro y hy
  rw [h _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy), Matrix.mulVec_mulVec, ← GlobalTheory.FinPlLoc.mt_mul, mul_inv_cancel, mt_one',
    Matrix.one_mulVec]

theorem moves_conj {S : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {t : GA D S} {L M : Lat S} (h : Moves S t L M P) (κ : GA D S) :
    Moves S (t⁻¹ * κ * t) L L P ↔ Moves S κ M M P := by
  constructor
  · intro h1
    have := moves_trans (moves_trans (moves_symm h) h1) h
    rwa [show t * (t⁻¹ * κ * t * t⁻¹) = κ by group] at this
  · intro h1
    have := moves_trans (moves_trans h h1) (moves_symm h)
    rwa [← mul_assoc] at this

theorem mem_St_mul {n : ℕ} (g β x : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) : x ∈ St (g * β) ↔ g⁻¹ * x * g ∈ St β := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hy ⊢
    rw [show x = g * (g⁻¹ * x * g) * g⁻¹ by group, ← hy]
    group

section Chain

variable {u : D.what₂.Word} {d : GlobalTheory.SeeSaw.Dat D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {ι : Type} (o : GlobalTheory.FinPl.OffDat d k ι) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d o.τ PP.1)
  (F : Formalism.L2.Forms.Forms0 D u)

def ChainFacts (L : Lat (D.sp.Y 0)) (b : GlobalTheory.SeeSaw.BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS) : Prop :=
  ∃ M : Lat b.V₀,
    (∀ v, v ∉ d.c.S → IsSelfDualC b.V₀ M ∧ MonoAt b.d L M v ∧ PrimAt d.c.ψ b.d L v ∧ LastAt d.c.ψ b.d (vecB b.o b.ζ) L M v) ∧
    (∀ v, v ∉ d.c.S → ¬ o.atT v → ∃ LL, IsSelfDualC b.L LL ∧ OrthAt b.o M (d.x 0).L LL v) ∧
    (∀ i, ∃ β₀ : GlobalTheory.FinPl.Frame (o.p i) b.V₀ (Fin (D.sp.X 0).rank ⊕ Fin 1), IsSumFrame b.o b.ζ (o.β 0 i) β₀ ∧
      β₀.IsLat M (GlobalTheory.LatPair.gluedS o.q 1 (o.Q 0 i).ker (o.Q 0 i).vec)) ∧
    (∀ PP, valuation (G PP).k ((G PP).q.pr (incA D (star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ))) = 1 ∧
      WShape (G PP).q b.d b.o b.ζ L (fun i => ((((G PP).S.ϖ : (G PP).kˣ) : (G PP).k) ^ (i.1 + 1))⁻¹)
        (fun i => ((((G PP).S.ϖ : (G PP).kˣ) : (G PP).k) ^ (2 * D.R.rS - i.1 + 1))⁻¹)
        (((((G PP).S.ϖ : (G PP).kˣ) : (G PP).k) ^ (D.R.rS + 1))⁻¹) 1 (d.x 0).L) ∧
    ∀ v, v ∉ d.c.S → ∀ a ∈ grpAt (D.sp.X 0) (· = v), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F), GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = y.1.1 →
      ((y : GL _ _) ∈ F.cls0.lev.U ↔ Moves (D.sp.Y 0) (embA b.d b.o a) L L (· = v))

end Chain

def toBes {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : SBes X h u ψ (D.sp.X 0)) : GlobalTheory.SeeSaw.BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS :=
  ⟨B.V₀, B.L, B.d, B.o, B.ζ, B.line, B.cpt, B.vN⟩

theorem eq_toBes {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : SBes X h u ψ (D.sp.X 0)) (b : GlobalTheory.SeeSaw.BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS)
    (v : Vol (D.sp.X 0)) (e : B.lev = b.lev v) : b = toBes B := by
  obtain ⟨V₀, L, dd, o, ζ, line, cpt, vN⟩ := b
  obtain ⟨V₀', L', dd', o', ζ', line', cpt', vA', vN', t1, t2, t3⟩ := B
  cases e
  rfl

theorem stab_read (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (β : GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β (latS D)) (κ : GA D (D.sp.Y 0)) :
    ((iotaX X h κ).1 = 1 ↔ κ ∈ GfC (D.sp.Y 0)) ∧ ((iotaX X h κ).2 ∈ X.B.I.Kset ↔ finE (D.sp.Y 0) κ ∈ St β) :=
  ⟨(GlobalTheory.SeeConjReadIota.read_iota X h β hβ κ).1, (GlobalTheory.SeeConjReadIota.read_iota X h β hβ κ).2.1⟩

theorem kset_conj (I : AutInst) {x : I.Gf} (hx : x ∈ I.Kset) (y : I.Gf) : x * y * x⁻¹ ∈ I.Kset ↔ y ∈ I.Kset := by
  have hm : ∀ {a b : I.Gf}, a ∈ I.Kset → b ∈ I.Kset → a * b ∈ I.Kset := fun {a b} ha hb => by
    show ((a * b : I.Gf) : GL _ _) ∈ Formalism.UG.stabGL I.Lf
    rw [Subgroup.coe_mul]
    exact mul_mem ha hb
  have hi : ∀ {a : I.Gf}, a ∈ I.Kset → a⁻¹ ∈ I.Kset := fun {a} ha => by
    show ((a⁻¹ : I.Gf) : GL _ _) ∈ Formalism.UG.stabGL I.Lf
    rw [Subgroup.coe_inv]
    exact inv_mem ha
  refine ⟨fun h => ?_, fun h => hm (hm hx h) (hi hx)⟩
  have := hm (hm (hi hx) h) hx
  rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this

theorem stab_of_frame (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word)
    (β : GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D)) (g t z : GA D (D.sp.Y 0))
    (hz : z ∈ Subgroup.center (GA D (D.sp.Y 0))) (hβ : Formalism.L2.DIV.IsFrame (finE (D.sp.Y 0) (z * g * t) * β) (latS D))
    (κ : GA D (D.sp.Y 0)) :
    (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) (((iotaX X h).symm (1, X.xu u))⁻¹ * g * t) * β)) ↔
      ((iotaX X h κ).1 = 1 ∧ (iotaX X h κ).2 ∈ X.B.I.Kset) := by
  have hR := stab_read X h _ hβ
  have e3 : (iotaX X h ((iotaX X h).symm (1, X.xu u) * κ * ((iotaX X h).symm (1, X.xu u))⁻¹)).2 =
      X.xu u * (iotaX X h κ).2 * (X.xu u)⁻¹ := by
    rw [map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]
    rfl
  generalize (iotaX X h).symm (1, X.xu u) = x at e3 ⊢
  have e1 : finE (D.sp.Y 0) (x⁻¹ * g * t) * β = finE (D.sp.Y 0) (z * x)⁻¹ * (finE (D.sp.Y 0) (z * g * t) * β) := by
    have e0 : (z * x)⁻¹ * (z * g * t) = x⁻¹ * g * t := by group
    rw [← mul_assoc, ← map_mul, e0]
  have e2 : (finE (D.sp.Y 0) (z * x)⁻¹)⁻¹ * finE (D.sp.Y 0) κ * finE (D.sp.Y 0) (z * x)⁻¹ = finE (D.sp.Y 0) (x * κ * x⁻¹) := by
    have := Subgroup.mem_center_iff.1 hz (x * κ * x⁻¹)
    have e0 : z * x * κ * (z * x)⁻¹ = x * κ * x⁻¹ :=
      calc z * x * κ * (z * x)⁻¹ = z * (x * κ * x⁻¹) * z⁻¹ := by group
        _ = x * κ * x⁻¹ := by rw [← this]; group
    rw [← map_inv, ← map_mul, ← map_mul, inv_inv, e0]
  rw [e1, mem_St_mul, e2, ← (hR _).2, e3, kset_conj _ (X.xu_K u), (hR κ).1]


end GlobalTheory.Core.Mi.LatMatch

end
