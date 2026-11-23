module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedThetaFunctionsReadOfMovedVacuumReads
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact

theorem closeTo_of_mul {D : D7} {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} {g : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)}
    {g' : GL (Fin N') (Formalism.MainNotions.StandardLatticesGL3.AE D)} {z z' : Matrix (Fin N') (Fin N) D.host.E} (m k : ℕ)
    (h : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc (m * k) g g' z z') : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc m g g' z z' := by
  intro i j
  obtain ⟨y, hy, e⟩ := h i j
  refine ⟨(k : Formalism.MainNotions.StandardLatticesGL3.AE D) * y, ?_, by rw [e]; push_cast; ring⟩
  rw [← nsmul_eq_mul]; exact nsmul_mem hy k

theorem exists_closeTo {D : D7} {cc : Ideal (𝓞 D.host.K)} (hc : cc ≠ ⊥) {N N' : ℕ} (g : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D))
    (g' : GL (Fin N') (Formalism.MainNotions.StandardLatticesGL3.AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) (n : ℕ) (hn : 0 < n) :
    ∃ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n g g' z z' := by
  obtain ⟨c, hc1, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  obtain ⟨a, ha0, ha⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (GlobalTheory.NormSum.MovedLattice.inverseHalfDifferent_ne_zero D)
  set b : D.host.E := ((c : D.host.K) : D.host.E) * algebraMap (𝓞 D.host.E) D.host.E a with hb
  set_option synthInstance.maxHeartbeats 200000 in
  have hb0 : b ≠ 0 := by
    refine mul_ne_zero ?_ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 ha0)
    intro h0
    apply hc0
    have : (c : D.host.K) = 0 := by exact_mod_cast h0
    exact_mod_cast this
  obtain ⟨v, hv⟩ : ∃ v, Formalism.MainNotions.StandardLatticesGL3.inc D b * v = 1 := by
    have hb1 : b * b⁻¹ = 1 := mul_inv_cancel₀ hb0
    exact ⟨Formalism.MainNotions.StandardLatticesGL3.inc D b⁻¹, by rw [← map_mul, hb1, map_one]⟩
  set t : Matrix (Fin N') (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D) := (g' : Matrix (Fin N') (Fin N') (Formalism.MainNotions.StandardLatticesGL3.AE D)) *
    z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) * ((g⁻¹ : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with ht
  choose e w hw he using fun i j => GlobalTheory.NormSum.Expand.approx (t i j * v) n hn
  refine ⟨Matrix.of fun i j => e i j * b, fun i j => ⟨Formalism.MainNotions.StandardLatticesGL3.inc D b * w i j,
    AddSubgroup.subset_closure ⟨c, hc1, _, ha, w i j, hw i j, rfl⟩, ?_⟩⟩
  have h1 : t i j * v * Formalism.MainNotions.StandardLatticesGL3.inc D b = t i j := by
    rw [mul_assoc, mul_comm v, hv, mul_one]
  rw [Matrix.sub_apply, ← ht, Matrix.map_apply, Matrix.of_apply, map_mul]
  linear_combination (Formalism.MainNotions.StandardLatticesGL3.inc D b) * he i j + h1

theorem reads_om_of_vacuum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d) →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ (c : ℂ) (f₀ : WO S T → ℂ), Reads ψ θ hS hT cc δ r e0 f₀ → Reads ψ θ hS hT cc δ r (c • W.Om x y e0) (om (g, h) f₀) →
  ∀ G ∈ TT D (tor0 D cc δ) a d, ∀ f, Reads ψ θ hS hT cc δ r G f → Reads ψ θ hS hT cc δ r (c • W.Om x y G) (om (g, h) f) := by
  intro D ψ θ S T a d hS hT cc δ r hSet e0 W χS χT om hW he0 x y g h hg hh c f₀ hf₀ hc G hG f hf
  have hC := hSet.crv
  have hSD0 : ∀ N : ℕ, Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D N) := by
    intro N
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    rw [← h2]; exact (h1 1).2
  obtain ⟨-, hWL, hint, -⟩ := GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC a d
    (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D cc δ) a d) (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)
  have hfix : ∀ v ∈ Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D cc δ) a d, Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) v e0 = e0 := by
    intro v hv
    rw [hWL v hv]; funext w; exact he0.2 v hv w
  have heT : e0 ∈ TT D (tor0 D cc δ) a d :=
    ⟨he0.1, 1, one_pos, fun v hv => by rw [one_nsmul]; exact hfix v hv⟩
  have hTT : ∀ z, Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0 ∈ TT D (tor0 D cc δ) a d := by
    intro z
    obtain ⟨Q, hQ, hz⟩ := GlobalTheory.NormSum.RatExtend.exists_nsmul_mem hC.1.1 δ z
    refine ⟨GlobalTheory.NormSum.RatExtend.Wd_diff _ he0.1, Q, hQ, fun v hv => ?_⟩
    obtain ⟨m, hm⟩ := hint v hv _ hz
    rw [GlobalTheory.NormSum.RatExtend.Hf_nsmul_right, ← GlobalTheory.NormSum.RatExtend.Hf_nsmul_left] at hm
    rw [GlobalTheory.NormSum.RatExtend.Wd_comm _ _ m hm, hfix _ (nsmul_mem hv _)]
  have hRt : ∀ (F : VC D a d → ℂ) (f' : WO S T → ℂ), Reads ψ θ hS hT cc δ r F f' → ∀ z,
      Reads ψ θ hS hT cc δ r (Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F)
        (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) • heisO ψ S T (finPt hS hT r z) f') := by
    intro F f' hF z
    exact (_root_.GlobalTheory.NormExact.heisO_finPt_reads ψ θ S T hS hT cc δ r hSet F f' hF z).smul _
  have hR0 : Reads ψ θ hS hT cc δ r (0 : VC D a d → ℂ) (0 : WO S T → ℂ) :=
    ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  have hRsum : ∀ {k : ℕ} (rr : Fin k → ℂ) (F : Fin k → VC D a d → ℂ) (f' : Fin k → WO S T → ℂ),
      (∀ i, Reads ψ θ hS hT cc δ r (F i) (f' i)) →
        Reads ψ θ hS hT cc δ r (∑ i, rr i • F i) (∑ i, rr i • f' i) := by
    intro k rr F f' hF
    have : ∀ s : Finset (Fin k), Reads ψ θ hS hT cc δ r (∑ i ∈ s, rr i • F i) (∑ i ∈ s, rr i • f' i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hR0
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact ((hF i).smul (rr i)).add ih
    exact this Finset.univ
  have key : ∀ zz : Matrix (Fin d) (Fin a) D.host.E, ∃ z',
      W.Om x y (Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ zz) e0) =
        Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') (W.Om x y e0) ∧
      Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ zz) • om (g, h) (heisO ψ S T (finPt hS hT r zz) f₀) =
        Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') • heisO ψ S T (finPt hS hT r z') (om (g, h) f₀) := by
    intro zz
    obtain ⟨m, hm, hl⟩ := W.lift x y zz e0 heT
    obtain ⟨n, hn, hL⟩ := _root_.GlobalTheory.MovedTr.moved_translate ψ θ S T hS hT cc δ r hSet χS χT om hW x y g h hg hh f₀ hf₀.1 zz
    obtain ⟨z', hz'⟩ := exists_closeTo hC.1.1 (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D))
      zz (m * n) (Nat.mul_pos hm hn)
    refine ⟨z', hl z' (closeTo_of_mul m n hz'), hL z' (closeTo_of_mul n m ?_)⟩
    rwa [mul_comm] at hz'
  choose z' hz1 hz2 using key
  obtain ⟨k, rr, z, rfl⟩ := GlobalTheory.ThetaSpan.theta_span D cc δ hC a d e0 he0 W.nz G hG
  have hfG := Reads.unique hf (hRsum rr _ _ fun i => hRt e0 f₀ hf₀ (z i))
  subst hfG
  have e1 : c • W.Om x y (∑ i, rr i • Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0) =
      ∑ i, rr i • Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z' (z i))) (c • W.Om x y e0) := by
    rw [(GlobalTheory.NormSum.RatExtend.Om_sum W x y Finset.univ rr _ fun i => hTT (z i)).2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz1, GlobalTheory.NormSum.RatExtend.Wd_smul, smul_comm]
  have e2 : om (g, h) (∑ i, rr i • (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) •
        heisO ψ S T (finPt hS hT r (z i)) f₀)) =
      ∑ i, rr i • (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z' (z i))) •
        heisO ψ S T (finPt hS hT r (z' (z i))) (om (g, h) f₀)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, hz2]
  rw [e1, e2]
  exact hRsum rr _ _ fun i => hRt _ _ hc (z' (z i))

end GlobalTheory.NormExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutationAtSmallPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem perm_of_isDC {G : Type} [Group G] (J : Subgroup G) (x : G) (A : Finset G) (h : Bridge.IsDC J x A) (κ : G)
    (hκ : κ ∈ J) : ∃ σ : Equiv.Perm A, ∀ s : A, ((σ s : A) : G)⁻¹ * κ * s ∈ J := by
  classical
  have hex : ∀ s : A, ∃ a : A, (a : G)⁻¹ * (κ * s) ∈ J := by
    intro s
    obtain ⟨k₁, k₂, hs⟩ := h.1 s s.2
    obtain ⟨a, ⟨ha, haJ⟩, -⟩ := h.2 (κ * s) ⟨⟨κ, hκ⟩ * k₁, k₂, by rw [hs]; simp [mul_assoc]⟩
    exact ⟨⟨a, ha⟩, haJ⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro s s' hss
    have h1 := hf s
    have h2 := hf s'
    rw [hss] at h1
    have h3 : (s : G)⁻¹ * s' ∈ J := by
      have := J.mul_mem (J.inv_mem h1) h2
      simpa [mul_assoc] using this
    obtain ⟨k₁, k₂, hs'⟩ := h.1 s' s'.2
    have hu := (h.2 s' ⟨k₁, k₂, hs'⟩).unique ⟨s.2, h3⟩ ⟨s'.2, by simp [J.one_mem]⟩
    exact Subtype.ext hu
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun s => ?_⟩
  simpa [mul_assoc] using hf s

theorem map_ev_eq_one_of_loc : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V) {l : ℕ} [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → ((l : ℕ) : 𝓞 D.host.E) ∉ (pl i.1.1).asIdeal → isLocEnv V pl ok i x → ((x : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map ev = 1 := by
  intro D V Pl0 pl ok i x l _ inc ev hev hl hx
  obtain ⟨e, α, he, -, hs, hxα⟩ := hx
  obtain ⟨v, ε, ⟨a, rfl, -, ha⟩, hf, hv⟩ := GlobalTheory.VacLat.place_of_primeIdem (Or.inl ⟨he, rfl⟩)
  have h0 : ev (a ⊗ₜ[D.host.F] 1) = 0 := by
    refine hev.2.2.1 a fun v' hv' => ha v' ?_
    rintro rfl
    apply hl
    rw [← hv] at hv'
    have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((l : ℕ) : 𝓞 D.host.F) ∈ (pl i.1.1).asIdeal := hv'
    rwa [map_natCast] at h1
  have h2 := GlobalTheory.SplitHeckeAdj.map_eq_one_of_supp (ev.comp (Formalism.L2.Theta.finPart D)) (e + Formalism.L2.Theta.cA D e)
    (by rw [hf]; exact h0) (Formalism.L2.Theta.mt V α) hs
  rw [hxα]
  exact h2

theorem chi_move {G : Type} [Group G] (J Lc : Subgroup G) (χ : J →* ℂˣ)
    (l2 : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ l ∈ Lc, Commute k₂ l)
    (l3 : ∀ k : J, (k : G) ∈ Lc → χ k = 1) (κ κ' : J) (a s : G) (ha : a ∈ Lc) (hs : s ∈ Lc)
    (h : (κ' : G) = a⁻¹ * κ * s) : χ κ' = χ κ := by
  obtain ⟨k₁, h₁, k₂, h₂, hL, hk, hc⟩ := l2 κ κ.2
  have e1 : κ = ⟨k₁, h₁⟩ * ⟨k₂, h₂⟩ := Subtype.ext hk
  have e2 : ((κ' * (⟨k₂, h₂⟩ : J)⁻¹ : J) : G) = a⁻¹ * k₁ * s := by
    show (κ' : G) * k₂⁻¹ = _
    rw [h, hk, mul_assoc a⁻¹, mul_assoc k₁, (hc s hs).eq]; group
  have e3 := l3 (κ' * (⟨k₂, h₂⟩ : J)⁻¹) (e2 ▸ Lc.mul_mem (Lc.mul_mem (Lc.inv_mem ha) hL) hs)
  rw [map_mul, map_inv, mul_inv_eq_one] at e3
  rw [e3, e1, map_mul, l3 ⟨k₁, h₁⟩ hL, one_mul]


set_option maxHeartbeats 1600000 in
theorem levChi_eq_of_loc : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (i : (blk p j t).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → ∀ (κ κ' : levJ p j t) (a s : Bridge.Gf (Vc D j)), a ∈ hkA p j t i → s ∈ hkA p j t i → (κ' : Bridge.Gf (Vc D j)) = a⁻¹ * κ * s → levChi p j t κ' = levChi p j t κ := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t i h1 h2 κ κ' a s ha hs h
  have hb := p.charW.base
  have ha' : isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok t) i a := (p.R.B.L j t).hecke.hA_loc i ⟨h1, h2⟩ a ha
  have hs' : isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok t) i s := (p.R.B.L j t).hecke.hA_loc i ⟨h1, h2⟩ s hs
  refine hb.fam.tie.elim fun _ x => x.elim fun _ x => x.elim fun _ tie => ?_
  refine (hb.lev.βV j).elim fun c hc => ?_
  rw [one_pow] at hc
  refine ha'.elim fun e x => x.elim fun _ x => ?_
  have he := x.1
  have hsp := (tie.ok t _).1 (show (p.P.A3.A.ok t) × ℕ from i).1.2
  have hl := GlobalTheory.SplitHeckeAdj.local_group (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) hc _ e he
    fun PP hP => GlobalTheory.SplitHeckeAdj.off_of_splitOff hsp PP (hP.elim (fun h1 => Or.inl (hb.fam.Sb h1)) Or.inr)
  refine hl.elim fun Lc l => ?_
  have hA : a ∈ Lc := (GlobalTheory.SplitHeckeAdj.loc_supp _ ha' he).elim fun g hg => hg.2 ▸ l.1 g hg.1
  have hS : s ∈ Lc := (GlobalTheory.SplitHeckeAdj.loc_supp _ hs' he).elim fun g hg => hg.2 ▸ l.1 g hg.1
  exact chi_move _ Lc _ l.2.1 l.2.2.1 κ κ' a s hA hS h

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem chi_cancel {K R : Type} [Field K] [CommRing R] (io : K ≃+* ℂ) (emb : R →+* K) (hinj : Function.Injective emb)
    (u u' : Rˣ) (X X' : K) (hXX : X' = X) (hX : X ≠ 0) (c c' : ℂ) (hcc : c' = c) (hc : c ≠ 0)
    (e1 : io (emb u' * X') * c' = 1) (e2 : io (emb u * X) * c = 1) : u' = u := by
  subst hXX hcc
  have e4 := io.injective (mul_right_cancel₀ hc (e1.trans e2.symm))
  exact Units.ext (hinj (mul_right_cancel₀ hX e4))

theorem perm_core (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (i : (blk p j t).Pl × ℕ)
    (hR : 1 ≤ i.2 ∧ i.2 ≤ (Vc D j).rank) (κ : levJ p j t) :
    ∃ σ : Equiv.Perm (hkA p j t i), ∀ s : hkA p j t i, ((σ s : hkA p j t i) : Bridge.Gf (Vc D j))⁻¹ * κ * s ∈ levJ p j t := by
  have h : Bridge.IsDC (levJ p j t) ((p.R.B.L j t).hecke.hx i) (hkA p j t i) := (p.R.B.L j t).hecke.hDC i hR
  exact perm_of_isDC (levJ p j t) ((p.R.B.L j t).hecke.hx i) (hkA p j t i) h κ κ.2

theorem perm_gen (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ}
    (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool) (io : PadicAlgCl l ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    (Lf : IntermediateField ℚ_[l] (PadicAlgCl l))
    (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j t →* (intR Lf)ˣ)
    (hev : ∀ τ, EvOk (incOf D e0 b τ) (ev τ)) (hkap : KapEq p j t ev bs rk kap) (hchi : ChiEq p j t io sh kap chi)
    (i : Ix p j t l N) (κ : levJ p j t) :
    ∃ σ : Equiv.Perm (hkA p j t i.1), ∀ s : hkA p j t i.1, ∃ κ' : levJ p j t,
      (κ : Bridge.Gf (Vc D j)) * (s : Bridge.Gf (Vc D j)) = (σ s : Bridge.Gf (Vc D j)) * κ' ∧ kap κ' = kap κ ∧
        chi κ' = chi κ := by
  have hN : N = (Vc D j).rank := Fin.equiv_iff_eq.mp ⟨rk.toEquiv⟩
  have hR : 1 ≤ i.1.2 ∧ i.1.2 ≤ (Vc D j).rank := ⟨i.2.1, by rw [← hN]; exact i.2.2.1⟩
  have hp := perm_core p j t i.1 hR κ
  refine hp.elim fun σ hσ => ?_
  have hinj : Function.Injective (intEmb Lf) := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  have loc : ∀ y ∈ hkA p j t i.1, ∀ τ,
      ((y : GL (Fin (Vc D j).rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ) = 1 := by
    intro y hy τ
    have hy' : isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok t) i.1 y := (p.R.B.L j t).hecke.hA_loc i.1 hR y hy
    exact map_ev_eq_one_of_loc (Vc D j) p.R.pl (p.P.A3.A.ok t) i.1 y _ (ev τ) (hev τ) i.2.2.2 hy'
  have key : ∀ (κ' : levJ p j t) (a s : Bridge.Gf (Vc D j)), a ∈ hkA p j t i.1 → s ∈ hkA p j t i.1 →
      (κ' : Bridge.Gf (Vc D j)) = a⁻¹ * κ * s → kap κ' = kap κ ∧ chi κ' = chi κ := by
    intro κ' a s ha hs he
    have hmap : ∀ τ, (((κ' : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
        (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ) =
        (((κ : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
        (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ) := by
      intro τ
      have ha1 := loc a ha τ
      have hs1 := loc s hs τ
      have ha' : ((((a⁻¹ : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
          (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ)) = 1 := by
        have h0 : ((((a⁻¹ : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
            (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ)) *
            (((a : GL (Fin (Vc D j).rank)
            (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ)) = 1 := by
          rw [← Matrix.map_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
            Matrix.map_one _ (ev τ).map_zero (ev τ).map_one]
        rwa [ha1, mul_one] at h0
      rw [he]
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, ha', hs1, one_mul, mul_one]
    have hmat : ∀ τ, kapMat p j t ev bs rk κ' τ = kapMat p j t ev bs rk κ τ := by
      intro τ
      unfold kapMat matOf
      rw [hmap τ]
    have hK : kap κ' = kap κ := by
      funext τ
      apply Units.ext
      apply Matrix.ext
      intro a c
      apply hinj
      have h1 := (hkap κ' τ).trans ((hmat τ).trans (hkap κ τ).symm)
      exact congrFun (congrFun h1 a) c
    refine ⟨hK, ?_⟩
    have hL := levChi_eq_of_loc p j t i.1 hR.1 hR.2 κ κ' a s ha hs he
    have hX : (∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ ?_
      exact ((Matrix.GeneralLinearGroup.det (kap κ τ)).isUnit.map (intEmb Lf)).ne_zero
    have hXX : (∏ τ, intEmb Lf (kap κ' τ).val.det ^ sh τ) = ∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ :=
      congrArg (fun f : D.what₂.Tau → GL (Fin N) (intR Lf) => ∏ τ, intEmb Lf (f τ).val.det ^ sh τ) hK
    have hcc : ((levChi p j t κ' : ℂˣ) : ℂ) = ((levChi p j t κ : ℂˣ) : ℂ) := congrArg (fun z : ℂˣ => (z : ℂ)) hL
    have e1 : io (intEmb Lf (chi κ') * ∏ τ, intEmb Lf (kap κ' τ).val.det ^ sh τ) * ((levChi p j t κ' : ℂˣ) : ℂ) = 1 :=
      hchi κ'
    have e2 : io (intEmb Lf (chi κ) * ∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ) * ((levChi p j t κ : ℂˣ) : ℂ) = 1 :=
      hchi κ
    exact chi_cancel io (intEmb Lf) hinj (chi κ) (chi κ') (∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ)
      (∏ τ, intEmb Lf (kap κ' τ).val.det ^ sh τ) hXX hX ((levChi p j t κ : ℂˣ) : ℂ) ((levChi p j t κ' : ℂˣ) : ℂ) hcc
      (levChi p j t κ).ne_zero e1 e2
  refine ⟨σ, fun s => ⟨⟨((σ s : hkA p j t i.1) : Bridge.Gf (Vc D j))⁻¹ * κ * s, hσ s⟩, ?_, ?_, ?_⟩⟩
  · show (κ : Bridge.Gf (Vc D j)) * s = (σ s : Bridge.Gf (Vc D j)) * ((σ s : Bridge.Gf (Vc D j))⁻¹ * κ * s)
    group
  · exact (key _ _ _ (σ s).2 s.2 rfl).1
  · exact (key _ _ _ (σ s).2 s.2 rfl).2


set_option maxHeartbeats 800000 in
open Classical in
theorem permAt (p : PtAt ex Csz) (j : Fin D.R.m) (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    PermAt p j P w := by
  intro _ e0 b io ev bs rk sh Lf _ kap chi hC
  obtain ⟨-, -, -, hev, hkap, hchi⟩ := hC
  dsimp only [GlobalTheory.FrameOf.frameOf]
  intro i κ
  exact perm_gen p j (p.R.mu w) e0 b io ev bs rk sh Lf kap chi hev hkap hchi i κ

end Point

end GlobalTheory.FramePerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDepthSumRoundingOscillation
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
namespace GlobalTheory.RefSum

theorem nuBetween_sum_and_eLoc_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (cx : Lt1 Dw → ℕ), (∀ A B : Lt1 Dw → ℝ, (∀ f, FacBetween Xo la f (cx f) (A f) (B f)) → NuBetween Xo la cx (∑ f, A f) (∑ f, B f) ∧ ∃ n : ℕ, NuBetween Xo la cx n (n + (∑ f, (B f - A f) + 1))) ∧ ∀ b : ℝ, OscLe Xo c p cx b → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Comp Xo c), (letI := H.starRing; eLoc Y Z la cx ≤ (b : EReal)) := by
  intro E _ _ _ H Dw l Xo c p _ la cx
  letI := H.starRing
  have hcs : ∀ g : Lt1 Dw → ℝ, (((∑ f, g f : ℝ)) : EReal) = ∑ f, ((g f : ℝ) : EReal) := fun g =>
    map_sum (⟨⟨((↑) : ℝ → EReal), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) g Finset.univ
  refine ⟨fun A B hAB => ⟨fun T io e ho y => ⟨?_, fun ha => ?_⟩, ?_⟩, ?_⟩
  · rw [hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).1
  · rw [hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).2 ha
  · set s : ℝ := ∑ f, A f with hs
    refine ⟨⌊max 0 s⌋₊, fun T io e ho y => ⟨?_, fun ha => ?_⟩⟩
    · have h0 : (0 : EReal) ≤ nuP p y cx := Finset.sum_nonneg fun f _ =>
        (_root_.GlobalTheory.RefSum.facBetween_zero_boundAll E H Dw l Xo c p la f (cx f)).1 T io e ho y |>.1 |> fun h => by simpa using h
      have h1 : ((s : ℝ) : EReal) ≤ nuP p y cx := by
        rw [hs, hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).1
      have hn : ((⌊max 0 s⌋₊ : ℕ) : ℝ) ≤ max 0 s := Nat.floor_le (le_max_left _ _)
      rcases le_total 0 s with h | h
      · exact (EReal.coe_le_coe_iff.2 (hn.trans (max_eq_right h).le)).trans h1
      · exact (EReal.coe_le_coe_iff.2 (hn.trans (max_eq_left h).le)).trans (by simpa using h0)
    · have hu : nuP p y cx ≤ ((∑ f, B f : ℝ) : EReal) := by
        rw [hcs]; exact Finset.sum_le_sum fun f _ => (hAB f T io e ho y).2 ha
      refine hu.trans (EReal.coe_le_coe_iff.2 ?_)
      have hlt : max 0 s < ((⌊max 0 s⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have hsd : ∑ f, (B f - A f) = ∑ f, B f - s := by rw [Finset.sum_sub_distrib]
      have hm : s ≤ max 0 s := le_max_right _ _
      linarith
  · intro b hb O _ β Y Z
    obtain ⟨A, hA⟩ := hb la
    calc eLoc Y Z la cx ≤ ((((A : ℝ) + b : ℝ)) : EReal) - (((A : ℝ)) : EReal) :=
          EReal.sub_le_sub (nuPSup_le fun T io e ho y hy => (hA T io e ho y).2 hy.2)
            (le_nuPInf fun T io e ho y _ => (hA T io e ho y).1)
      _ = (b : EReal) := by rw [← EReal.coe_sub]; congr 1; ring

end GlobalTheory.RefSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
section
set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.GenCoef

variable (O : Type) [CommRing O] (N : ℕ)

def rowSubst (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) :
    MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Fin N × Fin N) R :=
  aeval fun v => ∑ b : Fin N, C (Y v.1 b) * X (b, v.2)

def dwAlg (ν : Fin N → ℕ) : Subalgebra O (Module.End O (dualWeyl O N N ν)) :=
  Algebra.adjoin O (Set.range (fun g : GL (Fin N) O => Formalism.UG.dualWeylRep O N N ν g) ∪ Set.range (GlobalTheory.ExpFrame.rowProj O N ν))

def Expr (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R] (Y : Matrix (Fin N) (Fin N) R) : Prop :=
  ∃ (n : ℕ) (r : Fin n → R) (p : Fin n → Module.End O (dualWeyl O N N ν)), (∀ i, p i ∈ dwAlg O N ν) ∧
    ∀ f : dualWeyl O N N ν, rowSubst O N R Y (f : MvPolynomial (Fin N × Fin N) O) =
      ∑ i, r i • MvPolynomial.map (algebraMap O R) (p i f : MvPolynomial (Fin N × Fin N) O)

def lowGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  fun a b => if a = b then 1 else if b < a then X (a, b) else 0

def diagGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  Matrix.diagonal fun a => X (a, a)

def upGen : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  fun a b => if a = b then 1 else if a < b then X (a, b) else 0

def lduHom : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Fin N × Fin N) O :=
  aeval fun v => (lowGen O N * diagGen O N * upGen O N) v.1 v.2

end GlobalTheory.GenCoef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaleRootOfPrint
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem isScale_pow_eq {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {c c' : ℂ}
    (h : IsScale Rl v₀ B c) (h' : IsScale Rl v₀ B c') : ∃ k : ℕ, k ≠ 0 ∧ c' ^ k = c ^ k := by
  obtain ⟨gR, cR0, cL0, hT, u, hu, hF⟩ := h
  obtain ⟨gR', cR0', cL0', hT', u', hu', hF'⟩ := h'
  have huu : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  subst huu
  obtain ⟨a, ⟨k, hk, hak⟩, ha⟩ := _root_.GlobalTheory.CoefRoot.coef_root _ _ _ _ _ _ _ _ _ _ _ _ _ hT hT' j
  obtain ⟨F, x, hx⟩ := _root_.GlobalTheory.CoeffNonvanish.exists_coefFn_ne_zero (FWT.lamV D j)
  have e1 := hF' F
  rw [ha] at e1
  erw [LinearMap.map_smul, LinearMap.map_smul, hF F] at e1
  have e2 := congrFun e1 x
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  have hc : c' = D.what₂.embLL a * c := by
    have h3 : D.what₂.embLL a * c * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x =
        c' * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x := by
      rw [mul_assoc]; exact e2
    exact (mul_right_cancel₀ hx h3).symm
  refine ⟨k, hk, ?_⟩
  rw [hc, mul_pow, ← map_pow, hak, map_one, one_mul]

end GlobalTheory.BigOn.Exp
end
end

