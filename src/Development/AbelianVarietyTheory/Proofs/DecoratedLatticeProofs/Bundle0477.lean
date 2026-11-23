module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0441
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryLastRowCongrOneMemLocalLevelLevelPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalTwist
section
noncomputable section

section Col

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG Formalism.UG.P GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.LevRead Matrix
open scoped TensorProduct

namespace GlobalTheory.FamTraceChiCol.ColRead

theorem lamJ_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {gp : Fin 2 → ℕ} (G : Formalism.L2.Forms.GLoc F E σ gp) (i : Fin 2) (h : (gp i : 𝓞 F) ∈ v.asIdeal)
    {w : HeightOneSpectrum (𝓞 E)} (ρ : 𝓞 E ⧸ w.asIdeal →+* Formalism.L2.Forms.kv F v)
    (hres : ∀ (z : AfE F E) (c : 𝓞 E ⧸ w.asIdeal), HasRes w (adAt F w z) c →
        ∃ hh : G.phi i v h (prV (E := E) v z) ∈ v.adicCompletionIntegers F,
          IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hh⟩ = ρ c)
    {xa : GL (Fin n) (AfE F E)} {A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.asIdeal)} (hA : IsRed w xa A)
    (χ : ℕ → MulChar (Formalism.L2.Forms.kv F v) ℂ) (k t : ℕ) (z : 𝓞 E)
    (hz : Ideal.Quotient.mk w.asIdeal z =
      ∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < k ∧ (y : ℕ) ≠ k then A x y else 0)
    (fr : GL (Fin n) (v.adicCompletion F)) (hfr : fr = 1) :
    ∃ w' : v.adicCompletionIntegers F, (w' : v.adicCompletion F) = G.phi i v h ((z : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∧
      Formalism.L2.Forms.lamJ (G.psi0 i v h) χ k t 0 k (Formalism.L2.Forms.redM F v (G.mat i v h fr (bc (prV (E := E) v) xa))) =
        G.psi0 i v h (IsLocalRing.residue _ w') := by
  subst hfr
  obtain ⟨hh, e⟩ := hres (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z : E)) _ (by rw [adAt_inclE]; exact hasRes_coe w z)
  refine ⟨⟨_, hh⟩, rfl, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, TC.GLev0.redM_mat G i h ρ hres hA, Formalism.L2.Forms.lamJ, Finset.range_zero, Finset.prod_empty, mul_one, hz, map_sum ρ]
  refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum ρ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [apply_ite ρ, map_zero]
  rfl

end GlobalTheory.FamTraceChiCol.ColRead

end Col

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

namespace GlobalTheory.FamTraceChiCol.ColRead

open GlobalTheory.SymBridge GlobalTheory.RootEx


set_option maxHeartbeats 1000000 in
theorem exists_close {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (V : HSp D) {n κ τ : ℕ} (hr : V.rank = n) (hn : n = κ) (F : Frame k V.rank (XIx (Fin κ) (Fin τ) 0)) (hF : IsStdFr xPos F)
    {x : GA D V} {y : GL (Fin n) (GlobalTheory.AdForm.EF D)} (hy : GlobalTheory.AdForm.finM V hr x = y.1)
    {A : Matrix (Fin n) (Fin n) (𝓞 D.host.E ⧸ PP.asIdeal)} (hA : LevRead.IsRed (F := D.host.F) PP y A)
    (g : GL (XIx (Fin κ) (Fin τ) 0) k) (hg : (mt V x).map q.pr = F.β * g.val * F.γ) :
    ∃ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z =
        (∑ a : Fin n, ∑ b : Fin n, if (a : ℕ) + 1 = b ∧ (b : ℕ) < κ ∧ (b : ℕ) ≠ κ then A a b else 0) ∧
      valuation k ((∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then g.val (Sum.inl (Sum.inl a)) (Sum.inl (Sum.inl b)) else 0) -
        (ofSplit q).pr (z : D.host.E)) < 1 := by
  subst hr
  subst hn
  obtain ⟨e, he, hβ⟩ := hF
  choose R hR hR' using hA
  have hM : ∀ i j, valuation k ((mt V x).map q.pr i j - q.pr (incA D (R i j))) < 1 := fun i j => by
    have h2 : y.1 i j = toEAf D (mt V x i j) := by
      rw [← hy]
      rfl
    have h3 := LevChi.val_pr_lt q hq (z := mt V x i j - incA D (R i j)) (by
      rw [RingHom.map_sub, ← h2, RingHom.map_sub]
      exact (congrArg (fun t => Valued.v (adAt D.host.F PP (y.1 i j) - t)) (adAt_inclE D.host.F PP _)).trans_lt (hR' i j))
    rwa [RingHom.map_sub] at h3
  have hgM : ∀ a b, g.val a b = (mt V x).map q.pr (e a) (e b) := fun a b => by
    have h1 : (mt V x).map q.pr * F.β = F.β * g.val := by rw [hg, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    have h2 := congrFun (congrFun h1 (e a)) b
    rw [hβ] at h2
    simpa [Matrix.mul_apply, Matrix.one_apply] using h2.symm
  have he' : ∀ a : Fin V.rank, e (Sum.inl (Sum.inl a)) = a := fun a => Fin.ext (he _)
  have hc : ∀ a b : Fin V.rank, ((a : ℕ) + 1 = b ∧ (b : ℕ) < V.rank ∧ (b : ℕ) ≠ V.rank) ↔ b.val = a.val + 1 := fun a b =>
    ⟨fun h => h.1.symm, fun h => ⟨h.symm, b.2, b.2.ne⟩⟩
  refine ⟨∑ a : Fin V.rank, ∑ b : Fin V.rank, if b.val = a.val + 1 then R a b else 0, ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [apply_ite (Ideal.Quotient.mk PP.asIdeal), map_zero, hR]
    exact if_congr (hc a b).symm rfl rfl
  · let φ : 𝓞 D.host.E →+* k := (q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)
    have hφ : ∀ r : 𝓞 D.host.E, (ofSplit q).pr (r : D.host.E) = φ r := fun _ => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ, map_sum φ, ← Finset.sum_sub_distrib]
    refine (valuation k).map_sum_lt one_ne_zero fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum φ, ← Finset.sum_sub_distrib]
    refine (valuation k).map_sum_lt one_ne_zero fun b _ => ?_
    split_ifs
    · rw [hgM, he', he']
      exact hM a b
    · rw [map_zero, sub_zero, map_zero]
      exact zero_lt_one

end GlobalTheory.FamTraceChiCol.ColRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.TopFrame

theorem sumE_one_single {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) (t : Eˣ) (r b : Fin N) :
    GlobalTheory.TopStep.sumE hN (1 : Formalism.L2.Col.Sp E n ≃ₗ[E] Formalism.L2.Col.Sp E n) t (Pi.single b 1) r =
      if r.val = b.val then (if r.val + 1 = N then (t : E) else 1) else 0 := by
  rcases GlobalTheory.TopStep.idx_cases hN r with ⟨i, rfl⟩ | rfl
  · have h := congrFun (GlobalTheory.TopStep.prH_sumE hN (1 : Formalism.L2.Col.Sp E n ≃ₗ[E] Formalism.L2.Col.Sp E n) t (Pi.single b 1)) i
    refine h.trans ?_
    show (Pi.single b (1 : E) : Fin N → E) (Formalism.L2.Col.Br.iC hN i) = _
    have hi : ¬ (Formalism.L2.Col.Br.iC hN i).val + 1 = N := by
      show ¬ i.val + 1 = N
      have := i.2
      omega
    rw [if_neg hi, Pi.single_apply]
    simp only [Fin.ext_iff]
  · have hi : (Formalism.L2.Col.Br.iL hN).val + 1 = N := by
      show n + 1 = N
      omega
    rw [GlobalTheory.TopStep.sumE_last, if_pos hi, Pi.single_apply]
    simp only [Fin.ext_iff]
    split_ifs <;> simp

theorem frsF_top {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) (hA : A.Is) (hI : I.Ok) (P : BadPr I a) (hP : P.1 ∉ (B.primes X).vGs)
    (j : ℕ) (hj : j = B.R.m) (β : Ch₀ j) (r b : Fin (B.R.N j)) :
    Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j β).1.1 P (Pi.single b 1) r =
      if r.val = b.val then (if r.val + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0 := by
  subst hj
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have hPr := (base_fields_primes_ok B X).2.1
  have hπ := GlobalTheory.Mem.Col2.PerLaw.piT_notMem_Q hI u a
  have h1 := hA.top β (Formalism.L2.Col.DecoF.base _ _ _ _ _) 1 1 (isPtOf_base _)
    ⟨(Matrix.one_mul _).trans (Matrix.mul_one _).symm, Matrix.one_mulVec _⟩
  rw [one_mul] at h1
  have h2 := h1.fr ⟨P.1, hQ⟩ r b
  have h3 := (hA.base _ le_rfl β).1.fr ⟨P.1, hSQ⟩ r b
  have h4 := (algebraMap B.fields.E (P.1.adicCompletion B.fields.E)).injective (h3.symm.trans h2)
  rw [frsF_eq_ptFr, ← extTo_fr I.SQ _ ⟨P.1, hSQ⟩, h4, tilF_fr I.sel (I.tup a) hPr u hπ]
  refine (sumE_one_single _ _ r b).trans ?_
  rw [unitOf_val (hπ ⟨P.1, hQ⟩)]


end GlobalTheory.Fam.TopFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitFormUnitaryIntegralEntriesOfLevelLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitLevelInt

theorem entry_mem_of_levelVL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J = 1 → ∀ (t : 𝓞 E), (t : E) ≠ 0 → ∀ (Λ : Submodule (𝓞 E) (Fin n → E)), (∀ x, x ∈ Λ ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)), g ∈ Formalism.UG.levelVL σ J v Λ → ∀ i j, g.1 i j ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring := by
  intro F E _ _ _ _ _ σ hσ n J hJ t ht Λ hΛ v g hg
  subst hJ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro i; exact i.elim0
  haveI : NeZero n := ⟨by omega⟩
  have hlast : ∀ j : Fin n, j.1 + 1 = n ↔ j = Formalism.L2.Col.lastIdx n := by
    intro j
    constructor
    · intro h; ext; simp [Formalism.L2.Col.lastIdx]; omega
    · rintro rfl; simp [Formalism.L2.Col.lastIdx]; omega
  have hΛeq : Λ = Formalism.L2.Col.rll_dLat n ((t : E)⁻¹) := by
    ext x
    rw [hΛ, Formalism.L2.Col.rll_mem_dLat]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, ?_⟩
      · obtain ⟨r, hr, -⟩ := h i
        exact ⟨r, hr.symm⟩
      · obtain ⟨r, hr, hd⟩ := h (Formalism.L2.Col.lastIdx n)
        obtain ⟨q, rfl⟩ := hd ((hlast _).2 rfl)
        refine ⟨q, ?_⟩
        rw [hr]
        show (q : E) = (t : E)⁻¹ * ((t * q : 𝓞 E) : E)
        rw [show ((t * q : 𝓞 E) : E) = (t : E) * q from rfl, inv_mul_cancel_left₀ ht]
    · rintro ⟨h1, q, hq⟩
      intro j
      by_cases hj : j = Formalism.L2.Col.lastIdx n
      · subst hj
        refine ⟨t * q, ?_, fun _ => dvd_mul_right t q⟩
        have hq' : (q : E) = (t : E)⁻¹ * x (Formalism.L2.Col.lastIdx n) := hq
        rw [show ((t * q : 𝓞 E) : E) = (t : E) * q from rfl, hq', mul_inv_cancel_left₀ ht]
      · obtain ⟨r, hr⟩ := h1 j hj
        exact ⟨r, hr.symm, fun h => absurd ((hlast j).1 h) hj⟩
  set S := Formalism.BasicNotions.intV E v with hSdef
  let ι := Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F)
  have hmem : ∀ z : Fin n → E ⊗[F] v.adicCompletion F,
      z ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) S Λ ↔
        (∀ i, i ≠ Formalism.L2.Col.lastIdx n → z i ∈ S) ∧ ι (t : E)⁻¹ * z (Formalism.L2.Col.lastIdx n) ∈ S := by
    intro z
    rw [hΛeq]
    exact Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v _ (inv_ne_zero ht) z
  have htS : ι (t : E) ∈ S := GlobalTheory.UnitLocLastRow.inclE_int v t
  have hcols : ∀ h : GL (Fin n) (E ⊗[F] v.adicCompletion F),
      h ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (v.adicCompletion F) S Λ) →
      ∀ i j, j ≠ Formalism.L2.Col.lastIdx n → (i ≠ Formalism.L2.Col.lastIdx n → h.1 i j ∈ S) ∧
        ι (t : E)⁻¹ * h.1 (Formalism.L2.Col.lastIdx n) j ∈ S := by
    intro h hh i j hj
    have he : (Pi.single j 1 : Fin n → E ⊗[F] v.adicCompletion F) ∈
        Formalism.UG.latS (F := F) (v.adicCompletion F) S Λ := by
      rw [hmem]
      refine ⟨fun k _ => ?_, ?_⟩
      · by_cases hk : k = j
        · subst hk; rw [Pi.single_eq_same]; exact one_mem _
        · rw [Pi.single_eq_of_ne hk]; exact zero_mem _
      · rw [Pi.single_eq_of_ne (Ne.symm hj), mul_zero]; exact zero_mem _
    have h2 := (hmem _).1 ((hh _).1 he)
    rw [Matrix.mulVec_single_one] at h2
    exact ⟨fun hi => h2.1 i hi, h2.2⟩
  have hlastcol : ∀ i, ι (t : E) * g.1 i (Formalism.L2.Col.lastIdx n) ∈ S ∧
      (i = Formalism.L2.Col.lastIdx n → g.1 i (Formalism.L2.Col.lastIdx n) ∈ S) := by
    intro i
    have he : (Pi.single (Formalism.L2.Col.lastIdx n) (ι (t : E)) : Fin n → E ⊗[F] v.adicCompletion F) ∈
        Formalism.UG.latS (F := F) (v.adicCompletion F) S Λ := by
      rw [hmem]
      refine ⟨fun k hk => ?_, ?_⟩
      · rw [Pi.single_eq_of_ne hk]; exact zero_mem _
      · rw [Pi.single_eq_same, ← map_mul, inv_mul_cancel₀ ht, map_one]; exact one_mem _
    have h2 := (hmem _).1 ((hg.2 _).1 he)
    have e : ∀ k, ((g.1 : Matrix (Fin n) (Fin n) _) *ᵥ
        (Pi.single (Formalism.L2.Col.lastIdx n) (ι (t : E)) : Fin n → E ⊗[F] v.adicCompletion F)) k =
          g.1 k (Formalism.L2.Col.lastIdx n) * ι (t : E) := by
      intro k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    refine ⟨?_, fun hi => ?_⟩
    · by_cases hi : i = Formalism.L2.Col.lastIdx n
      · subst hi
        have := h2.2
        rw [e, mul_comm (g.1 _ _), ← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul] at this
        exact mul_mem htS this
      · have := h2.1 i hi
        rw [e, mul_comm] at this
        exact this
    · subst hi
      have := h2.2
      rw [e, mul_comm (g.1 _ _), ← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul] at this
      exact this

  have hU : Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) g.1 * g.1 = 1 := by
    have h1 := hg.1
    change Formalism.UG.cT _ g.1 * ((1 : Matrix (Fin n) (Fin n) E).map ι) * g.1 = (1 : Matrix (Fin n) (Fin n) E).map ι at h1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h1
    exact h1
  have hinv : ((g⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) = Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) g.1 :=
    Units.inv_eq_of_mul_eq_one_left hU
  have hginv := hcols g⁻¹ (inv_mem hg.2)
  intro i j
  by_cases hj : j = Formalism.L2.Col.lastIdx n
  · subst hj
    by_cases hi : i = Formalism.L2.Col.lastIdx n
    · exact (hlastcol i).2 hi
    · have h3 := (hginv (Formalism.L2.Col.lastIdx n) i hi).2
      rw [hinv] at h3
      change ι (t : E)⁻¹ * Formalism.UG.sigR σ (v.adicCompletion F) (g.1 i (Formalism.L2.Col.lastIdx n)) ∈ S at h3
      have h4 := GlobalTheory.UnitLocLastRow.sigR_mem_intV σ v h3
      rw [map_mul, GlobalTheory.UnitLocLastRow.sigR_sigR σ hσ, GlobalTheory.UnitLocLastRow.sigR_inclE] at h4
      have hs : ι (σ (t : E)) ∈ S := by
        have := GlobalTheory.UnitLocLastRow.sigR_mem_intV σ v htS
        rwa [GlobalTheory.UnitLocLastRow.sigR_inclE] at this
      have hst : σ (t : E) ≠ 0 := by
        intro h0; apply ht
        have := congrArg σ h0
        rwa [hσ, map_zero] at this
      have e : g.1 i (Formalism.L2.Col.lastIdx n) = ι (σ (t : E)) * (ι (σ (t : E)⁻¹) * g.1 i (Formalism.L2.Col.lastIdx n)) := by
        rw [← mul_assoc, ← map_mul, map_inv₀, mul_inv_cancel₀ hst, map_one, one_mul]
      rw [e]
      exact mul_mem hs h4
  · have h2 := hcols g hg.2 i j hj
    by_cases hi : i = Formalism.L2.Col.lastIdx n
    · subst hi
      have e : g.1 (Formalism.L2.Col.lastIdx n) j = ι (t : E) * (ι (t : E)⁻¹ * g.1 (Formalism.L2.Col.lastIdx n) j) := by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
      rw [e]; exact mul_mem htS h2.2
    · exact h2.1 hi

end GlobalTheory.UnitLevelInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryLastRowCongrOneMemLocalLevelLevelPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lastRow_congr_one_mem_localLevel_levelPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ {n : ℕ} [NeZero n] {J : Matrix (Fin n) (Fin n) E}, J = 1 → ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (p q : 𝓞 E), (q : E) = σ (p : E) → (p : E) * (q : E) = (T : E) → IsCoprime p q → T ≠ 0 → S.Lb = Formalism.L2.Col.rll_dLat n ((p : E)⁻¹) → ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ Formalism.UG.UPts σ J (v.adicCompletion F) → (∀ r s, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) r s ∈ Formalism.BasicNotions.intV E v) → (∀ s, ∃ c ∈ Formalism.BasicNotions.intV E v, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) s - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) s = Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * c) → x ∈ S.Uloc v := by
  first | exact @GlobalTheory.UnitLocLastRow.mem_Uloc | exact GlobalTheory.UnitLocLastRow.mem_Uloc | (intros; apply GlobalTheory.UnitLocLastRow.mem_Uloc <;> assumption)
end

