module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0049

@[expose] public section

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

section Mod

variable (T : LocLat G Qp LL O) (A : ArcP n) (c : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
  (Rst : Finset (Fin d))

def Psub : Submodule O (Fin d → W.EE) where
  carrier := {f | f ∈ Msub W A c e Rst ∧
    ∃ g, InNL W T c e (abelian₂ W A c e) b g ∧ ∀ k, f k = algebraMap (LetA O n) W.EE W.π₀ * g k}
  add_mem' := by
    rintro f f' ⟨hf, g, hg, hfg⟩ ⟨hf', g', hg', hfg'⟩
    exact ⟨(Msub W A c e Rst).add_mem hf hf', g + g',
      Formalism.MainNotions.UnusedSlot80.UnivC.inNL_add W T A c e b hg hg', fun k => by simp [hfg k, hfg' k, mul_add]⟩
  zero_mem' := ⟨(Msub W A c e Rst).zero_mem, 0, Formalism.MainNotions.UnusedSlot80.UnivC.inNL_zero W T A c e b,
    fun k => by simp⟩
  smul_mem' := by
    rintro o f ⟨hf, g, hg, hfg⟩
    exact ⟨(Msub W A c e Rst).smul_mem o hf, fun k => o • g k,
      Formalism.MainNotions.UnusedSlot80.UnivC.inNL_smul W T A c e b o hg, fun k => by
        rw [Pi.smul_apply, hfg k, mul_smul_comm]⟩

theorem psub_of_pi0Lam [IsDomain O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hbij : Function.Bijective (algebraMap K₀ K)) (hA : A.OK) (hc : c ∈ A.cuts) (hT : Win W A T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T (c - ((A.len c : ℕ) : ZMod n)) b) (f : Fin d → W.EE)
    (hf : ∀ k, InFr W c (W.π₀ * abelian₂ W A c (A.len c)) 1 (f k)) (hs : ∀ k ∉ Rst, f k = 0) :
    f ∈ Psub W T A c (A.len c) b Rst := by
  obtain ⟨g, hg, hfg⟩ := nl_of_pi0Lam W hR hbij A hA c hc T hT b hb f hf
  exact ⟨⟨fun k => inFr1_of_pi0Lam W A c _ (hf k), hs⟩, g, hg, hfg⟩

end Mod

theorem piece_upd (H : ℕ → ℕ) (a : ZMod n) (e s : ℕ) (hs : s < e) (z r : LetA O n) (hr : r ∈ W.AΔ)
    (hz : z = ps W s ^ H s * r) :
    InId W a e (Function.update (fun t => -((H t : ℕ) : ℤ)) s (H s)) (ιE (letE a * z)) := by
  unfold InId
  have en := numI_upd W H e s hs (H s)
  have ed := denI_upd W H e s hs (H s)
  simp only [numI, denI] at en ed
  rw [en, ed]
  refine ⟨(∏ t ∈ (Finset.range e).erase s, ps W t ^ H t) * r,
    Subalgebra.mul_mem _ (Subalgebra.prod_mem _ fun t _ =>
      Subalgebra.pow_mem _ (Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) t) _) hr, ?_⟩
  rw [← map_mul, hz]
  congr 1
  simp only [Int.toNat_natCast, show (-((H s : ℕ) : ℤ)).toNat = 0 by omega, pow_zero, one_mul]
  ring

section
variable [IsDomain O]

omit [IsDomain O] in
theorem inId0_of_mem (H : ℕ → ℕ) (a : ZMod n) (e : ℕ) {z : LetA O n} (hz : z ∈ W.AΔ) :
    InId W a e (fun t => -((H t : ℕ) : ℤ)) (ιE (letE a * z)) := by
  unfold InId
  have h1 : (∏ s ∈ Finset.range e, ps W s ^ (-((H s : ℕ) : ℤ)).toNat) = 1 :=
    Finset.prod_eq_one fun s _ => by rw [show (-((H s : ℕ) : ℤ)).toNat = 0 by omega, pow_zero]
  rw [h1]
  refine ⟨(∏ s ∈ Finset.range e, ps W s ^ (-(-((H s : ℕ) : ℤ))).toNat) * z,
    Subalgebra.mul_mem _ (Subalgebra.prod_mem _ fun t _ =>
      Subalgebra.pow_mem _ (Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) t) _) hz, ?_⟩
  rw [← map_mul]; congr 1; ring

theorem killer_elem (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hKL : KillerLevCore W)
    (hS : PsStable W) (hRAT : CutU.RATCore W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (A : ArcP n) (a : ZMod n) (e : ℕ) (M : ℕ)
    (hM : ∀ s < e, A.Hs a e s ≤ M) (hInv : ∀ s < e, InvLevAt W s) (κc : ℕ) (u₀ r₀ : LetA O n) (u rs : ℕ → LetA O n)
    (hr₀ : r₀ ∈ W.AΔ) (hrs : ∀ s < e, rs s ∈ W.AΔ)
    (hsum : lA W ^ κc = u₀ + ∑ s ∈ Finset.range e, u s)
    (hu₀ : u₀ = (∏ t ∈ Finset.range e, ps W t ^ (2 * A.Hs a e t)) * r₀)
    (hus : ∀ s < e, u s = W.π₀ * (∏ t ∈ (Finset.range e).erase s, ps W t ^ (2 * A.Hs a e t)) * rs s)
    (y : W.EE) (hy : InFr W a 1 (abelian₂ W A a e) y) :
    ∃ (K : ℕ) (x : ℕ → O) (x₀ : O), InFr W a (W.π₀ * abelian₂ W A a e) 1
      (lE W K * PPγ W e (Finset.Ico (-(M : ℤ)) M) y -
        ∑ s ∈ Finset.range e, x s • ιE (letE a * u s) - x₀ • ιE (letE a * (abelian₂ W A a e * r₀))) := by
  set H : ℕ → ℕ := A.Hs a e with hH
  set Λ := abelian₂ W A a e with hΛ
  set JS : Finset ℤ := Finset.Ico (-(M : ℤ)) M with hJS
  set α0 : ℕ → ℤ := fun t => -((H t : ℕ) : ℤ) with hα0
  have hps := Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W)
  have hΛm : Λ ∈ W.AΔ := W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem (hps t) _
  have hy0 : InId W a e α0 y := (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A a e y).1 hy
  have hlev := fun s (hs : s < e) => lev_const W hKL hS hCA h5 a e H M hM y hy0 s hs (hInv s hs)
  choose! κs xs hks using hlev
  set K₁ := ∑ s ∈ Finset.range e, κs s with hK₁
  set x' : ℕ → O := fun s => ((PD.p : ℕ) : O) ^ (K₁ - κs s) * xs s with hx'
  have hum : ∀ s < e, u s ∈ W.AΔ := fun s hs => by
    rw [hus s hs]
    exact W.AΔ.mul_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W)
      (W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem (hps t) _)) (hrs s hs)
  set Y' := lE W (κc + K₁) * PPγ W e JS y - ∑ s ∈ Finset.range e, x' s • ιE (letE a * u s) with hY'
  have hPPm : InId W a e α0 (PPγ W e JS y) := inId_aeval W hS _ y hy0
  have hY'm : InId W a e α0 Y' :=
    inId_sub W (inId_lE W hPPm _) (inId_sum W _ _ fun s hs =>
      inId_smul W (inId0_of_mem W H a e (hum s (Finset.mem_range.1 hs))) _)
  obtain ⟨z', hz'm, hz'⟩ := (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A a e Y').2 hY'm
  obtain ⟨o', w', hw'm, hval⟩ := value0 W hR a z' hz'm
  set C0 := ιE (letE a * (Λ * r₀)) with hC0
  have hC0m : InId W a e α0 C0 := inId0_of_mem W H a e (W.AΔ.mul_mem hΛm hr₀)
  set Y := lE W κc * Y' - o' • C0 with hYdef
  have hYm : InId W a e α0 Y := inId_sub W (inId_lE W hY'm _) (inId_smul W hC0m _)
  have hYΛ : InFr W a 1 Λ Y := (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A a e Y).2 hYm

  have hlevel : ∀ s < e, InId W a e (Function.update α0 s (H s)) Y := by
    intro s hs
    have hsm : s ∈ Finset.range e := Finset.mem_range.2 hs
    have hdvu : ∀ t ∈ (Finset.range e).erase s, Dv W H s (u t) := by
      intro t ht
      obtain ⟨hts, htm⟩ := Finset.mem_erase.1 ht
      rw [hus t (Finset.mem_range.1 htm)]
      have := dv_prod W H 2 (by norm_num) ((Finset.range e).erase t) s
        (Finset.mem_erase.2 ⟨Ne.symm hts, hsm⟩) (hrs t (Finset.mem_range.1 htm))
      obtain ⟨r, hr, he⟩ := this
      exact ⟨W.π₀ * r, W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) hr, by rw [mul_assoc, he]; ring⟩
    have hdv0 : Dv W H s (lA W ^ κc - u s) := by
      have e1 : lA W ^ κc - u s = u₀ + ∑ t ∈ (Finset.range e).erase s, u t := by
        rw [hsum, ← Finset.add_sum_erase _ _ hsm]; ring
      rw [e1, hu₀]
      exact dv_add W (dv_prod W H 2 (by norm_num) _ s hsm hr₀) (dv_sum W _ _ hdvu)
    have hdvΛ : Dv W H s (Λ * r₀) := by
      have := dv_prod W H 1 le_rfl (Finset.range e) s hsm hr₀
      simpa [hΛ, abelian₂] using this
    have hdec : Y = lE W κc * (lE W κc * (lE W (K₁ - κs s) *
          (lE W (κs s) * PPγ W e JS y - ιE (letE a) * algebraMap O W.EE (xs s)))) +
        lE W κc * (x' s • ιE (letE a * (lA W ^ κc - u s))) -
        lE W κc * ∑ t ∈ (Finset.range e).erase s, x' t • ιE (letE a * u t) - o' • C0 := by
      have hK : κc + K₁ = κc + (K₁ - κs s) + κs s := by
        have : κs s ≤ K₁ := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hsm
        omega
      rw [hYdef, hY', ← Finset.add_sum_erase _ _ hsm, hK, lE_add', lE_add', hx']
      simp only [lE, lA, Algebra.smul_def, map_mul, map_sub, map_pow, map_natCast]
      ring
    rw [hdec]
    refine inId_sub W (inId_sub W (inId_add W ?_ ?_) ?_) ?_
    · exact inId_lE W (inId_lE W (inId_lE W (hks s hs) _) _) _
    · obtain ⟨r, hr, he⟩ := hdv0
      exact inId_lE W (inId_smul W (piece_upd W H a e s hs _ r hr he) _) _
    · refine inId_lE W (inId_sum W _ _ fun t ht => inId_smul W ?_ _) _
      obtain ⟨r, hr, he⟩ := hdvu t ht
      exact piece_upd W H a e s hs _ r hr he
    · obtain ⟨r, hr, he⟩ := hdvΛ
      exact inId_smul W (piece_upd W H a e s hs _ r hr he) _

  have hV : ∑ s ∈ Finset.range e, u s = W.π₀ *
      ∑ s ∈ Finset.range e, (∏ t ∈ (Finset.range e).erase s, ps W t ^ (2 * H t)) * rs s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hus s (Finset.mem_range.1 hs)]; ring
  have hΛ2 : Λ * (Λ * r₀) = u₀ := by
    rw [hu₀, ← mul_assoc, ← sq, hΛ, abelian₂, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← pow_mul, mul_comm]
  have hπ : InFr W a W.π₀ Λ Y := by
    refine ⟨lA W ^ κc * w' + algebraMap O (LetA O n) o' *
        ∑ s ∈ Finset.range e, (∏ t ∈ (Finset.range e).erase s, ps W t ^ (2 * H t)) * rs s,
      W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.KL.lA_mem W) _) hw'm)
        (W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.sum_mem fun s hs =>
          W.AΔ.mul_mem (W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem (hps t) _)
            (hrs s (Finset.mem_range.1 hs)))), ?_⟩
    have hE : ιE Λ * Y = ιE (lA W ^ κc * (letE a * 1 * z') -
        algebraMap O (LetA O n) o' * (letE a * (Λ * (Λ * r₀)))) := by
      have h1 : ιE Λ * Y = lE W κc * (ιE Λ * Y') - algebraMap O W.EE o' * (ιE Λ * C0) := by
        rw [hYdef, Algebra.smul_def]; ring
      rw [h1, hz', hC0, ← Formalism.MainNotions.UnusedSlot80.KL.ι_lE W κc, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
      simp only [← map_mul, ← map_sub]
      congr 1
      ring
    rw [hE]
    congr 1
    linear_combination (lA W ^ κc) * hval - (algebraMap O (LetA O n) o' * letE a) * hΛ2 +
      (algebraMap O (LetA O n) o' * letE a) * hsum + (algebraMap O (LetA O n) o' * letE a) * hV

  obtain ⟨f₁, f₂, hYf, hf₁, hf₂⟩ := hRAT hCA h5 A a e 1 (fun s => ((H s : ℕ) : ℤ)) le_rfl
    (fun s _ => ⟨by omega, le_rfl⟩) Y hYΛ
    (fun s hs => ⟨0, Y, 0, by simp [lE], by
      have := hlevel s hs
      unfold InId at this
      have en := numI_upd W H e s hs (H s)
      have ed := denI_upd W H e s hs (H s)
      simp only [numI, denI] at en ed
      rw [en, ed] at this
      exact this, ⟨0, W.AΔ.zero_mem, by simp⟩⟩)
    (fun _ => ⟨0, Y, 0, by simp [lE], hπ, ⟨0, W.AΔ.zero_mem, by simp⟩⟩)
  have hf₁' : InFr W a (W.π₀ * Λ) 1 f₁ := by
    have h1 : (∏ s ∈ Finset.range e, ps W s ^ (-((H s : ℕ) : ℤ)).toNat) = 1 :=
      Finset.prod_eq_one fun s _ => by rw [show (-((H s : ℕ) : ℤ)).toNat = 0 by omega, pow_zero]
    have h2 : (∏ s ∈ Finset.range e, ps W s ^ (((H s : ℕ) : ℤ)).toNat) = Λ := by
      rw [hΛ, abelian₂]; exact Finset.prod_congr rfl fun s _ => by rw [Int.toNat_natCast]
    rw [h1, h2, pow_one] at hf₁
    exact hf₁
  refine ⟨κc + (κc + K₁), fun s => ((PD.p : ℕ) : O) ^ κc * x' s, o', ?_⟩
  have hfin : lE W (κc + (κc + K₁)) * PPγ W e JS y -
      ∑ s ∈ Finset.range e, (((PD.p : ℕ) : O) ^ κc * x' s) • ιE (letE a * u s) -
        o' • ιE (letE a * (Λ * r₀)) = f₁ + f₂ := by
    rw [← hYf, hYdef, hY', hC0, lE_add']
    simp only [lE, Algebra.smul_def, map_mul, map_pow, map_natCast, Finset.mul_sum, mul_sub, mul_assoc]
  rw [hfin]
  obtain ⟨u₁, hu₁, e₁⟩ := hf₁'
  obtain ⟨u₂, hu₂, e₂⟩ := hf₂
  exact ⟨u₁ + u₂, W.AΔ.add_mem hu₁ hu₂, by rw [mul_add, e₁, e₂, ← map_add (f := _)]; congr 1; ring⟩

end

theorem single_mem_span {d : ℕ} {ι : Type} [Fintype ι] (V : ι → Fin d → W.EE) (k : Fin d) (x : W.EE)
    (i : ι) (hV : V i = Pi.single k x) : Pi.single k x ∈ Submodule.span O (Set.range fun j : Fin (Fintype.card ι) =>
      V ((Fintype.equivFin ι).symm j)) := by
  refine Submodule.subset_span ⟨Fintype.equivFin ι i, ?_⟩
  simp [hV]

theorem univGenCore_of' [IsDomain O] [IsPrincipalIdealRing O] [NeZero n]
    [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] [Fintype (K →ₐ[Qp] LL)]
    (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O))
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hKL : KillerLevCore W) (hS : PsStable W)
    (hRAT : CutU.RATCore W)
    (hInv : ∀ (A : ArcP n) (c : ZMod n), c ∈ A.cuts → ∀ s < A.len c, InvLevAt W s)
    (hFin : FinLev W) : Formalism.MainNotions.UnusedSlot80.UnivC.UnivGenCore PD W := by
  intro A m T₂ c hsit d b sol Rst hFO
  obtain ⟨hCA, h5, hAOK, hWin, -, hc⟩ := hsit
  have hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T₂ (c - ((A.len c : ℕ) : ZMod n)) b := hFO.1.1
  have hbij := hCA.1
  set e := A.len c with he
  set Λ := abelian₂ W A c e with hΛ
  set H : ℕ → ℕ := A.Hs c e with hH
  set M := ∑ s ∈ Finset.range e, H s with hMdef
  have hM : ∀ s < e, A.Hs c e s ≤ M := fun s hs =>
    Finset.single_le_sum (f := H) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  set JS : Finset ℤ := Finset.Ico (-(M : ℤ)) M with hJS
  set t : O := (PPO W e JS).eval 1 with ht
  set lR : O := ((PD.p : ℕ) : O) with hlR
  have hps := Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W)
  have hΛm : Λ ∈ W.AΔ := W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (hps s) _

  obtain ⟨κc, u₀, hu₀m, u, hum, hsum, ⟨r₀, hr₀, hu₀⟩, hus⟩ :=
    Formalism.MainNotions.UnusedSlot80.LevC.crtLev W hR e (fun t => 2 * H t)
  choose! rs hrs hus' using hus

  have hp0 := p_ne_zero_O' W
  have hU : PsUnitE W := Formalism.MainNotions.UnusedSlot80.KF.psUnitE_of W hR
    ⟨Formalism.MainNotions.UnusedSlot80.ToolsR.tools1 hR, Formalism.MainNotions.UnusedSlot80.ToolsR.tools2 hR hp0 hpu,
      Formalism.MainNotions.UnusedSlot80.ToolsR.tools3 hR, Formalism.MainNotions.UnusedSlot80.ToolsR.tools4 hR⟩
  have hΛU : IsUnit (ιE Λ) := by
    refine ⟨∏ s ∈ Finset.range e, (hU s).unit ^ H s, ?_⟩
    rw [Units.coe_prod, hΛ, abelian₂, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_pow]
  set Λi : W.EE := ((hΛU.unit⁻¹ : W.EEˣ) : W.EE) with hΛi
  have hΛinv : Λi * ιE Λ = 1 := by
    rw [hΛi]; nth_rewrite 2 [← hΛU.unit_spec]; exact Units.inv_mul _
  have hP := exists_gammaA_pi0_eq_pi0_mul_of_RingP W hR

  set Ms := Msub W A c e Rst with hMs
  set Ps := Psub W T₂ A c e b Rst with hPs
  set Is := Isub W T₂ A c e b Rst with hIs
  have hIM : Is ≤ Ms := fun f hf => hf.1

  obtain ⟨D, hD⟩ := hFin c e H
  set F : Fin d × Fin D → Fin d → W.EE := fun p => Pi.single p.1 (Λi * ιE (letE c * W.π₀ ^ (p.2 : ℕ)))
    with hF
  have hfg : Ms ≤ Submodule.span O (Set.range F) ⊔ Ps := by
    intro f hf
    have hdec : ∀ k, ∃ (cc : Fin D → O) (R : W.EE), InFr W c (W.π₀ * Λ) 1 R ∧ (k ∉ Rst → R = 0) ∧
        f k = ∑ j, cc j • (Λi * ιE (letE c * W.π₀ ^ (j : ℕ))) + R := by
      intro k
      by_cases hk : k ∈ Rst
      · obtain ⟨uu, huu, hfu⟩ := hf.1 k
        obtain ⟨cc, w, hw, hcw⟩ := hD uu huu
        rw [show (∏ t ∈ Finset.range e, ps W t ^ H t) = Λ from rfl] at hcw
        refine ⟨cc, ιE (letE c * (W.π₀ * Λ) * w), ⟨w, hw, by rw [map_one, one_mul]⟩,
          fun h => absurd hk h, ?_⟩
        have hsm : ∑ j, cc j • (Λi * ιE (letE c * W.π₀ ^ (j : ℕ))) =
            Λi * ιE (letE c * ∑ j : Fin D, algebraMap O (LetA O n) (cc j) * W.π₀ ^ (j : ℕ)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [Finset.mul_sum, map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
          simp only [map_mul]; ring
        have hfk : ιE Λ * f k = ιE (letE c * ∑ j : Fin D, algebraMap O (LetA O n) (cc j) * W.π₀ ^ (j : ℕ)) +
            ιE Λ * ιE (letE c * (W.π₀ * Λ) * w) := by
          rw [hfu, mul_one, hcw, map_add (f := _), ← map_mul]; congr 1; congr 1; ring
        rw [hsm]
        linear_combination Λi * hfk - (f k - ιE (letE c * (W.π₀ * Λ) * w)) * hΛinv
      · exact ⟨0, 0, ⟨0, W.AΔ.zero_mem, by simp⟩, fun _ => rfl, by simp [hf.2 k hk]⟩
    choose cc R hR1 hR2 hR3 using hdec
    have hRv : (fun k => R k) ∈ Ps :=
      psub_of_pi0Lam W T₂ A c b Rst hR hbij hAOK hc hWin hb _ hR1 fun k hk => hR2 k hk
    have hfeq : f = ∑ p : Fin d × Fin D, cc p.1 p.2 • F p + fun k => R k := by
      funext k
      rw [hR3 k, Pi.add_apply, Finset.sum_apply, Fintype.sum_prod_type]
      simp only [Pi.smul_apply, hF, Pi.single_apply]
      rw [Finset.sum_eq_single k]
      · simp
      · intro k' _ hk'; simp [Ne.symm hk']
      · simp
    rw [hfeq]
    exact Submodule.add_mem_sup (Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)) hRv

  set Cg : ℕ → W.EE := fun j => if j < e then ιE (letE c * u j) else ιE (letE c * (Λ * r₀)) with hCg
  set ιv := {k // k ∈ Rst} × Fin (e + 1)
  set vv : ιv → Fin d → W.EE := fun p => Pi.single p.1.1 (Cg p.2) with hvv
  set v' : Fin (Fintype.card ιv) → Fin d → W.EE := fun j => vv ((Fintype.equivFin ιv).symm j) with hv'
  have hvmem : ∀ k ∈ Rst, ∀ j < e + 1, Pi.single k (Cg j) ∈ Submodule.span O (Set.range v') :=
    fun k hk j hj => single_mem_span W vv k _ (⟨k, hk⟩, ⟨j, hj⟩) rfl

  have hK : ∀ f ∈ Is, ∃ K : ℕ, (lR ^ K * t) • f ∈ Submodule.span O (Set.range v') ⊔ Ps := by
    intro f hf
    obtain ⟨g₁, hg₁, hpp⟩ := pp_inv W hS hP T₂ A c e b (PPO W e JS) f hf.2
    have hke := fun k => killer_elem W hR hKL hS hRAT hCA h5 A c e M hM (hInv A c hc) κc u₀ r₀ u rs hr₀
      (fun s hs => hrs s hs) hsum hu₀ (fun s hs => hus' s hs) (f k) (hf.1.1 k)
    choose Kk xk x0k hRk using hke
    set Kt := ∑ k, Kk k with hKt
    have hKle : ∀ k, Kk k ≤ Kt := fun k => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    set Sv : Fin d → W.EE := ∑ k ∈ Rst, (∑ s ∈ Finset.range e,
        (lR ^ (Kt - Kk k) * xk k s) • (Pi.single k (Cg s) : Fin d → W.EE) +
          (lR ^ (Kt - Kk k) * x0k k) • (Pi.single k (Cg e) : Fin d → W.EE))
      with hSv
    set Rr : Fin d → W.EE := fun k => if k ∈ Rst then lE W (Kt - Kk k) *
        (lE W (Kk k) * PPγ W e JS (f k) - ∑ s ∈ Finset.range e, xk k s • ιE (letE c * u s) -
          x0k k • ιE (letE c * (Λ * r₀))) else 0 with hRr
    set D2 : Fin d → W.EE := fun k => lE W Kt * (ιE W.π₀ * g₁ k) with hD2
    have hSvm : Sv ∈ Submodule.span O (Set.range v') := by
      refine Submodule.sum_mem _ fun k hk => Submodule.add_mem _ (Submodule.sum_mem _ fun s hs => ?_) ?_
      · exact Submodule.smul_mem _ _ (hvmem k hk s (by have := Finset.mem_range.1 hs; omega))
      · exact Submodule.smul_mem _ _ (hvmem k hk e (by omega))
    have hRrm : Rr ∈ Ps := by
      refine psub_of_pi0Lam W T₂ A c b Rst hR hbij hAOK hc hWin hb _ (fun k => ?_) (fun k hk => by simp [hRr, hk])
      by_cases hk : k ∈ Rst
      · simp only [hRr, hk, ite_true]
        obtain ⟨w, hw, hwe⟩ := hRk k
        refine ⟨lA W ^ (Kt - Kk k) * w, W.AΔ.mul_mem (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.KL.lA_mem W) _) hw, ?_⟩
        rw [map_one, one_mul] at hwe ⊢
        rw [hwe, ← Formalism.MainNotions.UnusedSlot80.KL.ι_lE, ← map_mul]; congr 1; ring
      · simp only [hRr, hk, ite_false]; exact ⟨0, W.AΔ.zero_mem, by simp⟩
    have hf0 : ∀ k ∉ Rst, ιE W.π₀ * g₁ k = 0 := fun k hk => by
      rw [← hpp k, hf.1.2 k hk, map_zero, smul_zero, sub_zero]
    have hD2m : D2 ∈ Ps := by
      refine ⟨⟨fun k => ?_, fun k hk => by simp [hD2, hf0 k hk]⟩, fun k => lE W Kt * g₁ k, ?_, fun k => by
        simp only [hD2]; ring⟩
      · simp only [hD2]
        rw [← hpp k]
        refine (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).2 (inId_lE W (inId_sub W ?_ ?_) _)
        · exact inId_aeval W hS _ _ ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 (hf.1.1 k))
        · exact inId_smul W ((Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A c e _).1 (hf.1.1 k)) _
      · have := Formalism.MainNotions.UnusedSlot80.UnivC.inNL_mulι W T₂ A c e b (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.KL.lA_mem W) Kt) hg₁
        simpa only [Formalism.MainNotions.UnusedSlot80.KL.ι_lE] using this
    have hSvk : ∀ k, Sv k = if k ∈ Rst then (∑ s ∈ Finset.range e, (lR ^ (Kt - Kk k) * xk k s) • Cg s +
        (lR ^ (Kt - Kk k) * x0k k) • Cg e) else 0 := by
      intro k
      simp only [hSv, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
      by_cases hk : k ∈ Rst
      · rw [ite_eq_left hk, Finset.sum_eq_single k (fun k' _ hk' => by simp [Ne.symm hk']) (fun h => absurd hk h)]
        simp
      · rw [ite_eq_right hk, Finset.sum_eq_zero]
        intro k' hk'
        have : k ≠ k' := fun h => hk (h ▸ hk')
        simp [this]
    have key : ∀ k ∈ Rst, (lR ^ Kt * t) • f k = (∑ s ∈ Finset.range e, (lR ^ (Kt - Kk k) * xk k s) • Cg s +
        (lR ^ (Kt - Kk k) * x0k k) • Cg e) + (lE W (Kt - Kk k) *
        (lE W (Kk k) * PPγ W e JS (f k) - ∑ s ∈ Finset.range e, xk k s • ιE (letE c * u s) -
          x0k k • ιE (letE c * (Λ * r₀))) - lE W Kt * (ιE W.π₀ * g₁ k)) := by
      intro k hk
      have hsplit : lE W Kt = lE W (Kt - Kk k) * lE W (Kk k) := by
        rw [← lE_add', Nat.sub_add_cancel (hKle k)]
      have hCe : Cg e = ιE (letE c * (Λ * r₀)) := by simp [hCg]
      have hCs : ∑ s ∈ Finset.range e, (lR ^ (Kt - Kk k) * xk k s) • Cg s =
          lE W (Kt - Kk k) * ∑ s ∈ Finset.range e, xk k s • ιE (letE c * u s) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs => ?_
        have : s < e := Finset.mem_range.1 hs
        simp only [hCg, this, ite_true]
        rw [lE_smul, smul_smul]
      have e2 : t • f k = PPγ W e JS (f k) - ιE W.π₀ * g₁ k := by
        rw [← hpp k]; unfold PPγ; ring
      have e3 : (lR ^ Kt * t) • f k = lE W Kt * (t • f k) := by rw [lE_smul, smul_smul]
      have e4 : (lR ^ (Kt - Kk k) * x0k k) • Cg e = lE W (Kt - Kk k) * (x0k k • ιE (letE c * (Λ * r₀))) := by
        rw [hCe, lE_smul, smul_smul]
      rw [hCs, e4, e3, e2, hsplit]
      ring
    have heq : (lR ^ Kt * t) • f = Sv + (Rr - D2) := by
      funext k
      rw [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hSvk k]
      by_cases hk : k ∈ Rst
      · simp only [hRr, hD2, hk, ite_true]; exact key k hk
      · simp only [hRr, hD2, hk, ite_false, hf.1.2 k hk, smul_zero, hf0 k hk, mul_zero, sub_zero, add_zero]
    refine ⟨Kt, ?_⟩
    rw [heq]
    exact Submodule.add_mem_sup hSvm (Ps.sub_mem hRrm hD2m)
  have hsat : ∀ K : ℕ, ∀ f ∈ Ms, (lR ^ K * t) • f ∈ Ps → f ∈ Ps := by
    intro K f hf hKf
    obtain ⟨N, o, ho⟩ := eval_one_dvd_prime_pow W hKL hCA hinj hO2 e JS
    have h1 : (lR ^ (K + N)) • f ∈ Ps := by
      have := Ps.smul_mem o hKf
      rwa [smul_smul, show o * (lR ^ K * t) = lR ^ (K + N) by rw [pow_add, ← ho]; ring] at this
    obtain ⟨-, g, hg, hfg⟩ := h1
    obtain ⟨g', hg', hfg'⟩ := sat_l W hR T₂ A c e b (K + N) f hf.1 g hg (fun k => by
      rw [lE_smul]; exact hfg k)
    exact ⟨hf, g', hg', hfg'⟩
  obtain ⟨g₀, J, hg₀, hJ, hgen⟩ := gen_of_killer Ms Ps Is hIM F hfg lR t v' hK hsat
  refine ⟨g₀, J, ?_, fun i => ⟨(hJ i).1.1, (hJ i).1.2, (hJ i).2⟩, fun f hf1 hf2 hf3 => ?_⟩
  · calc g₀ ≤ Fintype.card ιv := hg₀
      _ = Rst.card * (e + 1) := by simp [ιv]
      _ ≤ m * Formalism.MainNotions.LocalTheoryWindows.ro A.ty A.len c * (A.len c + 1) := Nat.mul_le_mul_right _ hFO.2.1
  · obtain ⟨o, ho⟩ := hgen f ⟨⟨hf1, hf2⟩, hf3⟩
    obtain ⟨-, g, hg, hfg⟩ := ho
    refine ⟨o, g, hg, fun k => ?_⟩
    have := hfg k
    simpa [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] using this

end Formalism.MainNotions.UnusedSlot80.UGen
