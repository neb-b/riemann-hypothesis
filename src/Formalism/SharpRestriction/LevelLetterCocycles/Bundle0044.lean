module

public import Formalism.SharpRestriction.LevelLetterCocycles.JumpsInLetterOfEvenIndex
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0043
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DlOfQp
section
noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.GM

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD
  Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem filLev_anti (T : LocLat G Qp LL O) (i : ZMod n) :
    Antitone fun a : ℤ => Formalism.MainNotions.WachCoordinates.FilLev W T i 0 a := by
  intro a b hab
  exact Submodule.map_mono (Submodule.map_mono
    (inf_le_inf_right _ fun x hx => Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hab hx))

theorem ιDi_le_fil (hbij : Function.Bijective (algebraMap K₀ K)) (T : LocLat G Qp LL O) (i : ZMod n)
    (H : ℕ) (hJ : ∀ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i → ∀ a, IsJumpV PD T.ρ τ a → -(H : ℤ) ≤ a)
    (a : ℤ) (ha : a ≤ -(H : ℤ)) : Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i ≤ Formalism.MainNotions.WachCoordinates.FilLev W T i 0 a := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨τ, hτ, hover⟩ := Formalism.MainNotions.UnusedSlot80.LevC.tau_over W hbij i
  have h1 := Formalism.MainNotions.UnusedSlot80.LevC.fil_low W T i τ hover hbij.2 H (hJ τ hτ) hx
  have h2 := Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ ha h1
  refine ⟨x, ⟨x, ⟨h2, by simpa using hx⟩, by simp⟩, rfl⟩

theorem qp_smul_gE (hq : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (T : LocLat G Qp LL O)
    (h c : ℕ) {r : ℕ} (e' : Fin r → W.DD T) (Z : Matrix (Fin r) (Fin r) (PowerSeries O)) (k : Fin r) :
    Formalism.MainNotions.LiftingTheory.qp W ^ c • gE W T h c e' Z k = Formalism.MainNotions.LiftingTheory.qp W ^ h • ftE W T e' Z k := by
  unfold gE
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ c), smul_smul, map_pow, ← mul_pow,
    Ring.mul_inverse_cancel _ hq, one_pow, one_smul]

theorem qp_pow_inj (hq : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (T : LocLat G Qp LL O)
    (c : ℕ) (z : W.DD T) (hz : Formalism.MainNotions.LiftingTheory.qp W ^ c • z = 0) : z = 0 := by
  calc z = ((Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) ^ c *
        (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ c) • z := by
          rw [← mul_pow, Ring.inverse_mul_cancel _ hq, one_pow, one_smul]
    _ = (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) ^ c •
        (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ c) • z) := by rw [smul_smul, map_pow]
    _ = 0 := by rw [algebraMap_smul, hz, smul_zero]

theorem qp_mem_AΔ : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ :=
  W.AΔ.add_mem (Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.uniformizer_mem_delta_invariants W) (W.AΔ.natCast_mem _)

theorem dl_of_qp (hq : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (T : LocLat G Qp LL O)
    (i : ZMod n) (c : ℕ) (g y : W.DD T) (hgy : Formalism.MainNotions.LiftingTheory.qp W ^ c • g = y)
    (hy : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i y) : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i g := by
  constructor
  · apply sub_eq_zero.1
    apply qp_pow_inj W hq T c
    rw [smul_sub, smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ c) (letE i : LetA O n) g, hgy, hy.1, sub_self]
  · intro δ hδ
    apply sub_eq_zero.1
    apply qp_pow_inj W hq T c
    have hA : W.γA δ (Formalism.MainNotions.LiftingTheory.qp W ^ c) = Formalism.MainNotions.LiftingTheory.qp W ^ c :=
      W.AΔ.pow_mem (qp_mem_AΔ W) c δ hδ
    have e := Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γD_smulA W T δ (Formalism.MainNotions.LiftingTheory.qp W ^ c) g
    rw [hA, hgy, hy.2 δ hδ] at e
    rw [smul_sub, ← e, hgy, sub_self]

theorem ring_clauses_at_uniformizer (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.Ring9 W := by
  have hfin1 : finrank K₀ K = 1 := by
    have := (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq
    rw [Module.finrank_self] at this
    exact this.symm
  obtain ⟨-, -, h9'⟩ := h9 T hT hA.2.1 hA.2.2
  obtain ⟨hring, -⟩ := h9' hfin1
  exact hring

theorem gE_mem (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W) (hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W)
    {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ}
    (hS : SetCS W d T₁ T₂ F b S η m) (i : ZMod n) (hi : i ∈ evens n d)
    (e' : Fin (finrank LL T₂.V) → W.DD T₂) (m' : ℕ) (u : Fin m' → ℤ)
    (had : AdaptData W T₂ i (b i + S) η m e' m' u) (σ : ℕ) (Z : Matrix _ _ (PowerSeries O))
    (hZP : ZProps W T₂ i (b i + S + η) σ e' had.1 Z) (j : Fin m') (hmr : m' ≤ finrank LL T₂.V) :
    gE W T₂ (b i + S) ((b i + S : ℕ) + u j).toNat e' Z (Fin.castLE hmr j) ∈ NDl W T₂ i := by
  have hie : (i.val + d) % 2 = 0 := (Finset.mem_filter.1 hi).2
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hT : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hl11 : 11 ≤ PD.p := hS.2.1
  obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
  obtain ⟨-, hπu, w, hw⟩ := DetS.uniformizer_unit_and_q_factor W h9 hCA T₂ hT (by omega)
  have hq := DetS.qp_unit W hπu
  have hR9 := ring_clauses_at_uniformizer W h9 hCA T₂ hT
  obtain ⟨-, -, hmr', hwin, hfil, -⟩ := id had
  have hηb := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_eta_lt W hS i
  set h : ℕ := b i + S with hhdef
  set k : Fin (finrank LL T₂.V) := Fin.castLE hmr j with hkdef
  set c : ℕ := ((h : ℤ) + u j).toNat with hcdef
  have hc : (c : ℤ) = h + u j := Int.toNat_of_nonneg (by have := (hwin j).1; omega)

  have hyN : Formalism.MainNotions.LiftingTheory.qp W ^ h • ftE W T₂ e' Z k ∈ NDl W T₂ i := by
    unfold ftE
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun m₁ _ => ?_
    rw [smul_comm, pow_one]
    have hm := DetA.qpφ_mem W hE hC hQ h5 h9 hS i hie e' had.1 m₁
    have ha := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_mem_invariants W hR9 (Z m₁ k)
    refine ⟨(W.N T₂).smul_mem _ hm.1, ?_, fun δ hδ => ?_⟩
    · rw [smul_comm (letE i : LetA O n), hm.2.1]
    · rw [Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γD_smulA W T₂ δ, ha δ hδ, hm.2.2 δ hδ]
  have hgy := qp_smul_gE W hq T₂ h c e' Z k
  have hgDL := dl_of_qp W hq T₂ i c _ _ hgy hyN.2

  obtain ⟨u0, hlq, hu0⟩ := Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.lev_q_X_mul W i ζ hζ (by omega)
    (Formalism.MainNotions.N.Pv.LocalLengthBound.p_ne_zero_LL W)
  set U : PowerSeries LL := W.lev i ζ ((↑w⁻¹ : (LetA O n)ˣ) : LetA O n) * u0 with hUdef
  have hwq : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W) = PowerSeries.X * U := by
    have e : Formalism.MainNotions.LiftingTheory.qp W = ((↑w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.q := by
      rw [hw, ← mul_assoc, Units.inv_mul, one_mul]
    rw [e, map_mul, hlq, hUdef]; ring
  have hU : PowerSeries.constantCoeff U ≠ 0 := by
    rw [hUdef, map_mul]
    refine mul_ne_zero ?_ hu0
    exact (PowerSeries.isUnit_iff_constantCoeff.1 ((Units.isUnit _).map (W.lev i ζ))).ne_zero
  have hU0 : U ≠ 0 := fun h0 => hU (by rw [h0, map_zero])
  have hlevpow : ∀ t : ℕ, W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ t) = PowerSeries.X ^ t * U ^ t := by
    intro t; rw [map_pow, hwq, mul_pow]
  have hlevne : ∀ t : ℕ, W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ t) ≠ 0 := by
    intro t; rw [hlevpow]; exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (pow_ne_zero _ hU0)

  obtain ⟨hEx, hDi, -, -, hconv, -, -⟩ := hRu hCA T₂ hT i ζ hζ
  obtain ⟨df, hdf, -⟩ := hEx (ftE W T₂ e' Z k) _ hyN.1 (hlevne h)
  obtain ⟨dg, hdg, -⟩ := hEx (gE W T₂ h c e' Z k) (Formalism.MainNotions.LiftingTheory.qp W ^ c) (by rw [hgy]; exact hyN.1)
    (hlevne c)
  have hy1 := hconv (Formalism.MainNotions.LiftingTheory.qp W ^ h) _ df hdf
  have hy2 := hconv (Formalism.MainNotions.LiftingTheory.qp W ^ c) _ dg hdg
  rw [hgy] at hy2
  have huniq := (hEx (Formalism.MainNotions.LiftingTheory.qp W ^ h • ftE W T₂ e' Z k) 1 (by rw [one_smul]; exact hyN.1)
    (by rw [map_one]; exact one_ne_zero)).unique hy2 hy1
  obtain ⟨mg, hmg⟩ := hdg.1
  have hi1 : i - 1 + ((1 : ℕ) : ZMod n) = i := by push_cast; ring
  have hZ := hZP.2 k ζ hζ df (by rw [hi1]; exact hdf)
  have hv : ιV PD (LL := LL) (V := T₂.V) ((φVB PD (LL := LL) (V := T₂.V))^[1]
      (W.cmp T₂ ⟨e' k, (had.1.1 k).1⟩)) ∈ Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 (u j) := by
    rw [Function.iterate_one]; exact hfil j _
  set Fil : ℤ → Submodule LL (T₂.V ⊗[Qp] BdR) := fun a => Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 a with hFil
  have hanti : Antitone Fil := filLev_anti W T₂ i
  have hLBf : Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB 0 df := by
    intro t ht
    rw [hZ t (by omega), ite_eq_right (by omega)]
  set Ff := Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS (U ^ h) df with hFf
  set E := Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS (U ^ c) dg with hEdef
  have hF_mem : ∀ s : ℤ, s < ((h + η : ℕ) : ℤ) → Ff s ∈ Fil (u j) := by
    intro s hs
    rw [hFf, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_eq_sum hLBf (U ^ h) s (s.toNat + 1)
      (by have := Int.self_le_toNat s; omega)]
    refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
    rw [hZ _ (by omega)]
    split_ifs
    · exact Submodule.smul_mem _ _ hv
    · exact Submodule.zero_mem _
  have hF_neg : ∀ s : ℤ, s < 0 → Ff s = 0 := fun s hs =>
    Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hLBf (U ^ h) s hs
  have hEF : ∀ t : ℤ, E t = Ff (t + u j) := by
    intro t
    have e1 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ c)) dg = fun s => E (s - c) := by
      rw [hlevpow, Formalism.MainNotions.N.Pv.LocalLengthBound.conv_eq, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_mul hmg,
        Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_X_pow (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hmg _)]
    have e2 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ h)) df = fun s => Ff (s - h) := by
      rw [hlevpow, Formalism.MainNotions.N.Pv.LocalLengthBound.conv_eq, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_mul hLBf,
        Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_X_pow (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hLBf _)]
    have e3 := congrFun huniq (t + c)
    rw [e1, e2] at e3
    simp only at e3
    rw [show t + (c : ℤ) - c = t by ring, show t + (c : ℤ) - h = t + u j by omega] at e3
    exact e3
  have hEDi : ∀ t, E t ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i := fun t =>
    Formalism.MainNotions.N.Pv.LocalLengthBound.smulS_mem hmg _ (hDi _ dg hgDL hdg) (U ^ c) t
  have hlow : ∀ a : ℤ, a ≤ -(h : ℤ) → Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i ≤ Fil a := by
    intro a ha
    refine ιDi_le_fil W hCA.1 T₂ i h (fun τ hτ a' ha' => ?_) a ha
    have hw2 := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS i τ hτ a' ha'
    unfold JumpWinS at hw2
    rw [ite_eq_left hie] at hw2
    simp only [Set.mem_union, Set.mem_Icc] at hw2
    rw [hhdef]; push_cast at hw2 ⊢
    omega
  have hDgE : Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.Dg Fil 0 E := by
    intro t
    by_cases ht : t + u j < ((h + η : ℕ) : ℤ)
    · rw [hEF t]
      by_cases h0 : t + u j < 0
      · rw [hF_neg _ h0]; exact Submodule.zero_mem _
      · exact hanti (show 0 - t ≤ u j by omega) (hF_mem _ ht)
    · exact hlow (0 - t) (by have := (hwin j).2; push_cast at ht; omega) (hEDi t)
  have hUc : PowerSeries.constantCoeff (U ^ c) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hU
  have hdg_eq : dg = Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS (U ^ c)⁻¹ E :=
    (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_inv hmg (U ^ c) hUc).symm
  have hDg : Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.Dg Fil 0 dg := by
    rw [hdg_eq]
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.Dg_smulS hanti (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hmg _) hDgE _
  have hcrit := (hEC hCA T₂ hT i ζ hζ _ dg hgDL hdg).1 ⟨c, by rw [hgy]; exact hyN.1⟩
  refine ⟨hcrit.2 fun t => ?_, hgDL⟩
  have := hDg t
  simpa [hFil] using this

theorem gMem_of (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W) (hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W) : GMem W :=
  fun _ _ _ _ _ _ _ _ hS i hi e' m' u had σ Z hZP j hmr =>
    gE_mem W hE hC hQ h5 h9 hRu hEC hS i hi e' m' u had σ Z hZP j hmr

end Formalism.MainNotions.RamifiedCoefficientChains.S9.GM
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ExistsSmulPowEqSumOfInFNc
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

structure Ctx : Prop where
  hbij : Function.Bijective (algebraMap K₀ K)
  hs : W.s = 1
  hp2 : PD.p ≠ 2
  h5p : 5 ≤ PD.p
  hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W
  h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
    Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h
  h3 : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p3 W T
  hmod : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀
  hΔ : IsUnit ((W.DelF.card : ℕ) : O)
  hsat : SATcore W
  hsatP : SATPcore W
  hTr : Formalism.MainNotions.LiftingTheory.coreTr W
  hH : Formalism.MainNotions.LiftingTheory.coreH W
  hinj : Function.Injective (algebraMap O LL)
  hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x
  hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v
  hp0 : ((PD.p : ℕ) : O) ≠ 0

variable {W}

theorem Ctx.hCA (C : Ctx W) : Formalism.MainNotions.LiftingTheory.CaseA W := ⟨C.hbij, C.hs, C.hp2⟩

theorem exists_smul_pow_eq_sum_of_inFNc (C : Ctx W) (T : LocLat G Qp LL O) (A : ArcP n) (hA : A.OK) (hT : Win W A T) (a : ZMod n)
    (N₁ : ℕ) (hN₁ : Hw A.G₀ A.S A.η (A.ty (a + 1)) ≤ N₁) (x : W.DD T) (hx : InFNc W T (a + 1) 1 x) :
    ∃ (r : ℕ) (bb : Fin r → W.DD T) (β : Fin r → LetA O n), (∀ j, Formalism.MainNotions.LiftingTheory.InNΔi W T a (bb j)) ∧
      (∀ j, β j ∈ W.AΔ) ∧ ps W 0 ^ N₁ • x = ∑ j, β j • W.φD T (bb j) := by
  have h5T := C.h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
  obtain ⟨y, hyN, hya, rfl⟩ := hx
  rw [one_smul]
  have hyl : y ∈ W.Nl T (a + 1) := ⟨y, hyN.1, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hya⟩
  have h1 := Formalism.MainNotions.UnusedSlot80.ArcC.iter_down W C.hs T h5T (a + 1) 1 y hyl
  rw [Finset.prod_range_one, pow_zero, AlgHom.one_apply, Nat.cast_zero, sub_zero, Nat.cast_one,
    add_sub_cancel_right] at h1
  obtain ⟨w, hw, w', hww, -⟩ := q_unit W C.hR C.hp0
  have hp0w : ps W 0 = w' * W.q := by rw [hw, ← mul_assoc, mul_comm w', hww, one_mul]
  obtain ⟨dd, hdd⟩ := Nat.exists_eq_add_of_le hN₁
  have e1 : ps W 0 ^ N₁ • y = (w' ^ N₁ * W.q ^ dd) • (W.q ^ Hw A.G₀ A.S A.η (A.ty (a + 1)) • y) := by
    rw [hp0w, smul_smul, hdd]; congr 1; ring
  have h2 := Submodule.smul_mem _ (w' ^ N₁ * W.q ^ dd) h1
  rw [← e1] at h2
  obtain ⟨⟨r, bb0, hb0, huniq, -⟩, -⟩ := C.hmod T hT.1
  have h3 := Formalism.MainNotions.UnusedSlot80.ArcC.span_pow_le W T bb0 (fun z hz => (huniq z hz).exists) a 1 h2
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun (LetA O n)).1 h3
  have hbΔ : ∀ j, Formalism.MainNotions.LiftingTheory.InNΔi W T a ((letE a : LetA O n) • bb0 j) := fun j =>
    ⟨Formalism.MainNotions.UnusedSlot80.PhiPowers.smul_mem_NΔ W T (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) (hb0 j),
      ⟨bb0 j, (hb0 j).1, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩⟩
  have hp0Δ : ps W 0 ^ N₁ ∈ W.AΔ := W.AΔ.pow_mem (ps_mem_AΔ W C.hR.1 0) N₁
  obtain ⟨dd, hd, hzd⟩ := Formalism.MainNotions.WachCoordinates.Br.average C.hΔ cc
    (fun j => (W.φD T ^ 1 : Module.End O (W.DD T)) ((letE a : LetA O n) • bb0 j))
    (fun j δ hδ => φD_pow_Δ W T (hbΔ j).1.2 1 δ hδ)
    (fun δ hδ => (Formalism.MainNotions.UnusedSlot80.PhiPowers.smul_mem_NΔ W T hp0Δ hyN).2 δ hδ) hcc.symm
  refine ⟨r, fun j => (letE a : LetA O n) • bb0 j, dd, hbΔ, hd, ?_⟩
  rw [hzd]
  simp only [pow_one]

theorem up1 (C : Ctx W) (T : LocLat G Qp LL O) (A : ArcP n) (hA : A.OK) (hT : Win W A T) (a : ZMod n)
    (H : ℕ) (hH : Mw A.G₀ A.S A.η (A.ty (a + 1)) ≤ H) {vv : LetA O n} (hv : vv ∈ W.AΔ) (y : W.DD T)
    (hy : InFNc W T a 1 y) : InFNc W T (a + 1) 1 ((ps W 0 ^ H * vv) • W.φD T y) := by
  have h5T := C.h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
  obtain ⟨y', hy'N, hy'l, rfl⟩ := hy
  rw [one_smul]
  have hQ : W.Q = W.q := by simp [LocWach.Q, C.hs]
  have hyl : y' ∈ W.Nl T (a + 1 - 1) := by
    rw [add_sub_cancel_right]
    exact ⟨y', hy'N.1, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hy'l⟩
  have hM := h5T.1 (a + 1) y' hyl
  rw [hQ] at hM
  obtain ⟨w, hw, w', hww, -⟩ := q_unit W C.hR C.hp0
  have hp0w : ps W 0 = w' * W.q := by rw [hw, ← mul_assoc, mul_comm w', hww, one_mul]
  have hN : (ps W 0 ^ H * vv) • W.φD T y' ∈ W.N T := by
    obtain ⟨dd, hdd⟩ := Nat.exists_eq_add_of_le hH
    have e1 : (ps W 0 ^ H * vv) • W.φD T y' = (w' ^ H * W.q ^ dd * vv) •
        (W.q ^ Mw A.G₀ A.S A.η (A.ty (a + 1)) • W.φD T y') := by
      rw [hp0w, smul_smul]; congr 1; rw [hdd]; ring
    rw [e1]
    exact (W.N T).smul_mem _ hM
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ ((ps W 0 ^ H * vv) • W.φD T y') = (ps W 0 ^ H * vv) • W.φD T y' := by
    intro δ hδ
    rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', (W.AΔ.mul_mem (W.AΔ.pow_mem (ps_mem_AΔ W C.hR.1 0) H) hv) δ hδ,
      ← W.φγ_comm, hy'N.2 δ hδ]
  refine ⟨_, ⟨hN, hΔ⟩, ?_, by rw [one_smul]⟩
  rw [smul_comm]
  congr 1
  have := φD_pow_letter W T a y' hy'l 1
  simpa using this

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

