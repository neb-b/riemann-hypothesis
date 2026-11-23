module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0362
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0259
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0231

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdmissibilityWitnessesCongrModThetaLocal
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WitCong

open IsDedekindDomain Formalism.L2.SG.Pf.BBTie

theorem dvd_of_loc {E : Type} [Field E] [NumberField E] {g c : 𝓞 E} (hg : g ≠ 0)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), g ∈ P.asIdeal → ∃ s, s ∉ P.asIdeal ∧ g ∣ s * c) : g ∣ c := by
  classical
  let J : Ideal (𝓞 E) := Submodule.comap (LinearMap.mulRight (𝓞 E) c) (Ideal.span {g})
  have hJ : ∀ s, s ∈ J ↔ g ∣ s * c := fun s => by
    simp [J, Submodule.mem_comap, Ideal.mem_span_singleton]
  by_contra hnd
  have hJtop : J ≠ ⊤ := by
    intro htop
    apply hnd
    have h1 : (1 : 𝓞 E) ∈ J := htop ▸ Submodule.mem_top
    simpa using (hJ 1).1 h1
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJtop
  have hgJ : g ∈ J := (hJ g).2 (dvd_mul_right g c)
  have hMbot : M ≠ ⊥ := by
    intro hb
    have hgM := hJM hgJ
    rw [hb, Ideal.mem_bot] at hgM
    exact hg hgM
  obtain ⟨s, hsP, hs⟩ := h ⟨M, hM.isPrime, hMbot⟩ (hJM hgJ)
  exact hsP (hJM ((hJ s).2 hs))

theorem coeff_dvd {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (Λ : Submodule (𝓞 E) S.V) {g : ℕ} (hg0 : g ≠ 0) (F : LFlag S r T) (hz : F.fl.z ∈ Λ)
    (hFC : IsFixedConv Λ g F) (c : Fin (r + 1) → 𝓞 E)
    (hc : ModG S Λ g (∑ a, ((c a : 𝓞 E) : E) • frame F a)) (a : Fin (r + 1)) : (g : 𝓞 E) ∣ c a := by
  classical
  have hcoe : ∀ (o : 𝓞 E) (v : S.V), o • v = (o : E) • v := fun o v => by
    rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
  have horth : ∀ v : S.V, (∀ i, S.hT (F.fl.e i) v = 0) → v ∈ orth S (Xsp F) := by
    intro v hv
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    have hle : Xsp F ≤ LinearMap.ker (S.hT.flip v) := by
      show Submodule.span E (Set.range F.fl.e) ≤ _
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      simp [hv i]
    simpa using hle hx
  have hz_o : F.fl.z ∈ orth S (Xsp F) := horth _ F.fl.z_orth
  have hf_o : ∀ j, frame F j ∈ orth S (Xsp F) := by
    intro j
    induction j using Fin.lastCases with
    | last => simpa [frame, FlagG.fvec] using hz_o
    | cast i => simpa [frame, FlagG.fvec] using horth _ (fun k => F.fl.e_iso k i)
  have heX : ∀ i, F.fl.e i ∈ Xsp F := fun i => by
    show F.fl.e i ∈ Submodule.span E (Set.range F.fl.e)
    exact Submodule.subset_span ⟨i, rfl⟩
  have hxdec : ∑ a, ((c a : 𝓞 E) : E) • frame F a =
      ∑ i : Fin r, ((c i.castSucc : 𝓞 E) : E) • F.fl.e i + ((c (Fin.last r) : 𝓞 E) : E) • F.fl.z := by
    rw [Fin.sum_univ_castSucc]
    simp [frame, FlagG.fvec]
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg0
  have hgcoe : ((g : 𝓞 E) : E) = (g : E) := by
    rw [RingOfIntegers.coe_eq_algebraMap, map_natCast]
  have hgO : (g : 𝓞 E) ≠ 0 := fun h0 => hgE (by rw [← hgcoe, h0]; simp [RingOfIntegers.coe_eq_algebraMap])
  apply dvd_of_loc hgO
  intro P hgP
  haveI := P.isPrime
  obtain ⟨s, hs, hsx⟩ := hc P hgP
  have hsP : s ∉ P.asIdeal := hs
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hsx
  obtain ⟨l, hlΛ, hl⟩ := hsx
  have hlE : l = ((g : E)⁻¹ * (s : E)) • ∑ a, ((c a : 𝓞 E) : E) • frame F a := by
    have hl' : (g : E) • l = (s : E) • ∑ a, ((c a : 𝓞 E) : E) • frame F a := by
      rw [← hgcoe, ← hcoe, ← hcoe, hl]
    rw [mul_smul, ← hl', smul_smul, inv_mul_cancel₀ hgE, one_smul]
  have hlx : l = ∑ i : Fin r, ((g : E)⁻¹ * (s : E) * (c i.castSucc : E)) • F.fl.e i +
      ((g : E)⁻¹ * (s : E) * (c (Fin.last r) : E)) • F.fl.z := by
    rw [hlE, hxdec, smul_add, Finset.smul_sum]
    simp only [smul_smul]

  have hzL : ((g : E)⁻¹ * (s : E) * (c (Fin.last r) : E)) • F.fl.z ∈ Lsub Λ F := by
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · refine Submodule.mem_sup.2 ⟨l, ?_, -(∑ i : Fin r, ((g : E)⁻¹ * (s : E) * (c i.castSucc : E)) • F.fl.e i), ?_, ?_⟩
      · refine Submodule.mem_inf.2 ⟨hlΛ, ?_⟩
        show l ∈ orth S (Xsp F)
        rw [hlE]
        exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hf_o a))
      · show _ ∈ Xsp F
        exact neg_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (heX i))
      · rw [hlx]
        abel
    · show _ ∈ orth S (Xsp F)
      exact Submodule.smul_mem _ _ hz_o
  obtain ⟨o, ho⟩ := hFC.2 _ hzL
  induction a using Fin.lastCases with
  | last =>
    refine ⟨s, hsP, o, RingOfIntegers.ext ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast] at ho ⊢
    rw [ho]
    field_simp
  | cast j =>
    obtain ⟨cc, -, hcc1, hloc⟩ := hFC.1 P
    have hcc : ∀ i, cc i = 1 := hcc1 hgP
    set y : S.V := ∑ i : Fin r, ((g : E)⁻¹ * (s : E) * (c i.castSucc : E)) • F.fl.e i with hy
    have hyl : y = l - o • F.fl.z := by
      rw [hcoe, ho, hlx]
      abel
    have hyX : y ∈ XLam Λ F := by
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [hyl]
        exact Submodule.sub_mem _ hlΛ (Submodule.smul_mem _ _ hz)
      · show y ∈ Xsp F
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (heX i)
    have hyloc : y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) :=
      ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hyX⟩
    rw [hloc] at hyloc
    obtain ⟨s', hs', hs'y⟩ := hyloc
    have hs'P : s' ∉ P.asIdeal := hs'
    simp only [hcc, one_smul] at hs'y
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hs'y
    have hsum : ∑ i : Fin r, ((w i : E) - (s' : E) * ((g : E)⁻¹ * (s : E) * (c i.castSucc : E))) • F.fl.e i = 0 := by
      have h1 : ∑ i : Fin r, ((w i : 𝓞 E) : E) • F.fl.e i = (s' : E) • y := by
        rw [← hcoe, ← hw]
        exact Finset.sum_congr rfl fun i _ => (hcoe _ _).symm
      simp only [sub_smul, Finset.sum_sub_distrib, h1, hy, Finset.smul_sum, smul_smul]
      exact sub_self _
    have hj := Fintype.linearIndependent_iff.1 F.fl.e_indep _ hsum j
    refine ⟨s' * s, fun hm => (P.isPrime.mem_or_mem hm).elim hs'P hsP, w j, RingOfIntegers.ext ?_⟩
    rw [sub_eq_zero] at hj
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast] at hj ⊢
    rw [hj]
    field_simp

theorem wit_sub_dvd {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
    (Λ : Submodule (𝓞 E) S.V) {g : ℕ} (hg0 : g ≠ 0) (F : LFlag S r T) (F' : LFlag S r T') (hz : F.fl.z ∈ Λ)
    (hFC : IsFixedConv Λ g F) {ξ ξ' : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)}
    (h : AdmWit Λ g F F' ξ) (h' : AdmWit Λ g F F' ξ') (a b : Fin (r + 1)) : (g : 𝓞 E) ∣ (ξ - ξ') a b := by
  have hM : ModG S Λ g (∑ c, (((ξ - ξ') c b : 𝓞 E) : E) • frame F c) := by
    have heq : ∑ c, (((ξ - ξ') c b : 𝓞 E) : E) • frame F c =
        (frame F' b - frameAct (frame F) ξ' b) - (frame F' b - frameAct (frame F) ξ b) := by
      simp only [frameAct, Matrix.sub_apply, RingOfIntegers.coe_eq_algebraMap, map_sub, sub_smul,
        Finset.sum_sub_distrib]
      abel
    rw [heq]
    intro P hP
    exact sub_mem (h'.2.2 b P hP) (h.2.2 b P hP)
  exact coeff_dvd Λ hg0 F hz hFC (fun c => (ξ - ξ') c b) hM a

theorem witness_congr : ∀ (D : D7) (Z : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), IsRowLat D F0 Λ → Formalism.L2.SG.TermDef.PD D Λ (lf D F0) u' F' → ∀ ξ ξ' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), AdmWit Λ (gS D) (lf D F0) F' ξ → AdmWit Λ (gS D) (lf D F0) F' ξ' → ∀ (p : PlF D) (a b : Fin (D.R.rS + 1)), (D.s.atP p).ιE (((ξ * ξ'⁻¹) a b : 𝓞 D.host.E) : D.host.E) - (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b ∈ Submodule.span (Z.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Z.M p))} := by
  intro D Z u u' F0 Λ F' hR _hPD ξ ξ' hξ hξ' p a b
  obtain ⟨-, hFH, -⟩ := hR
  obtain ⟨-, -, hL, hFC⟩ := hFH
  have hg0 : gS D ≠ 0 := Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hdiff : ∀ c d, ((gS D : ℕ) : 𝓞 D.host.E) ∣ (ξ - ξ') c d :=
    fun c d => wit_sub_dvd Λ hg0 (lf D F0) F' hL.1 hFC hξ hξ' c d
  have hdet : IsUnit ξ'.det := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hji => hξ'.1 i j hji)]
    simp [hξ'.2.1]
  have hkey : ξ * ξ'⁻¹ - 1 = (ξ - ξ') * ξ'⁻¹ := by
    rw [Matrix.sub_mul, Matrix.mul_nonsing_inv _ hdet]
  have hdvd : ((gS D : ℕ) : 𝓞 D.host.E) ∣ (ξ * ξ'⁻¹ - 1) a b := by
    rw [hkey, Matrix.mul_apply]
    exact Finset.dvd_sum fun c _ => (hdiff a c).mul_right _
  obtain ⟨y, hy⟩ := hdvd
  have hsub : (D.s.atP p).ιE (((ξ * ξ'⁻¹) a b : 𝓞 D.host.E) : D.host.E) -
      (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b =
      ((gS D : ℕ) : (D.s.atP p).Ep) * (D.s.atP p).ιE (y : D.host.E) := by
    have h1 : (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b =
        (D.s.atP p).ιE (((1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) a b : 𝓞 D.host.E) :
          D.host.E) := by
      by_cases h : a = b <;> simp [Matrix.one_apply, h, RingOfIntegers.coe_eq_algebraMap]
    have h2 : (ξ * ξ'⁻¹) a b = (ξ * ξ'⁻¹ - 1) a b + (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1))
        (𝓞 D.host.E)) a b := by
      rw [Matrix.sub_apply, sub_add_cancel]
    rw [h1, h2, hy]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_add (f := _), map_mul, map_natCast, add_sub_cancel_right]
  obtain ⟨-, -, -, hO, -, hsp⟩ := Z.agree p
  have hyO : (D.s.atP p).ιE (y : D.host.E) ∈ (Z.M p).L.O := by
    rw [hO, (D.s.atP p).O_def]
    exact IsIntegral.tower_top ((RingOfIntegers.isIntegral_coe y).map (D.s.atP p).ιE.toIntAlgHom)
  have hgO : ((gS D : ℕ) : (D.s.atP p).Ep) * (D.s.atP p).ιE (y : D.host.E) ∈ (Z.M p).L.O :=
    mul_mem (natCast_mem _ _) hyO
  rw [hsub]
  unfold Formalism.MainNotions.S.LocNG.theta
  revert hsp
  cases hM : (Z.M p).split with
  | none =>
    intro _
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hgO⟩, ?_⟩
    simp [Subring.smul_def]
  | some gM =>
    cases hD : (D.s.atP p).split with
    | none =>
      intro h
      exact h.elim
    | some sg =>
      rintro ⟨-, hq⟩
      have hl := (D.s_split p).1 (by rw [hD]; rfl)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      have hθ : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (gM.q : (D.s.atP p).Fp) =
          ((Formalism.MainNotions.S.Loc.resChar p : ℕ) : (D.s.atP p).Ep) := by
        rw [hq, sg.q_eq, map_natCast]
      rw [hθ]
      rcases hl with hl | hl
      · refine Submodule.mem_span_singleton.2
          ⟨⟨((D.host.g 1 : ℕ) : (D.s.atP p).Ep) * (D.s.atP p).ιE (y : D.host.E),
            mul_mem (natCast_mem _ _) hyO⟩, ?_⟩
        rw [Subring.smul_def, smul_eq_mul, hl]
        simp only [gS, Nat.cast_mul]
        ring
      · refine Submodule.mem_span_singleton.2
          ⟨⟨((D.host.g 0 : ℕ) : (D.s.atP p).Ep) * (D.s.atP p).ιE (y : D.host.E),
            mul_mem (natCast_mem _ _) hyO⟩, ?_⟩
        rw [Subring.smul_def, smul_eq_mul, hl]
        simp only [gS, Nat.cast_mul]
        ring

end GlobalTheory.WitCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AlongFamilyOfMassRatio
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Finset

namespace GlobalTheory.CritLevel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sq_le_two_pow (k : ℕ) (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ 2 k]; nlinarith

theorem sizes_low {D : D7} (L : SizeData₂ D) (h : SizesAt L) : L.sc.x ≤ D.R.k ∧ Real.sqrt L.sc.b ≤ L.sc.b' := by
  obtain ⟨-, -, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hW, -⟩ := h
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  refine ⟨le_trans ?_ hK.1, le_trans hW ?_⟩
  · refine Real.self_le_rpow_of_one_le hx.le ?_
    unfold szTh
    linarith
  · have hn : (1 : ℝ) ≤ D.R.n := by
      have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
      exact_mod_cast this
    refine div_le_self ?_ (one_le_mul_of_one_le_of_one_le hx.le hn)
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity

theorem err_le (D : D7) {δ : ℝ} (hδ : 0 < δ) (h : 8 / Real.log (1 + δ) ≤ D.R.k) :
    Real.exp ((D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k)) - 1 ≤ δ := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hl : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast (show D.R.f ≤ D.R.k from D.R.f_le_k)
  have h2 : (D.R.k : ℝ) ^ 2 ≤ 2 ^ D.R.k := by exact_mod_cast sq_le_two_pow D.R.k (by omega)
  have e2 : (2 : ℝ) ^ ((3 : ℝ) - D.R.k) = 8 / 2 ^ D.R.k := by
    rw [Real.rpow_sub two_pos, Real.rpow_natCast]; norm_num
  rw [sub_le_iff_le_add', ← Real.le_log_iff_exp_le (by linarith), e2]
  rw [div_le_iff₀ hl] at h
  calc (D.R.f : ℝ) * (8 / 2 ^ D.R.k) ≤ D.R.k * (8 / (D.R.k : ℝ) ^ 2) := by gcongr
    _ = 8 / D.R.k := by field_simp
    _ ≤ _ := by rw [div_le_iff₀ (by linarith)]; linarith

theorem form_of_ranks (D : D7) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) (u : D.what₂.Word) (h3 : UnitaryVolumeMass.stLem3L0 D u) {C0 : ℝ}
    (hD : StandingNumericalData D C0) : UnitaryVolumeMass.FormAt D u := by
  intro F0 he hz what₂ hrows
  obtain ⟨-, -, -, -, -, -, -, -, hT, -⟩ := hD
  have hp := (D.mem u).A.T_prime
  have h3T : 3 ≤ (D.mem u).A.T := by
    have h1 := (hT u).2
    have h2 : 2 * 2 ≤ D.host.g 0 * D.host.g 1 :=
      Nat.mul_le_mul (D.host.g_prime 0).two_le (D.host.g_prime 1).two_le
    have h4 : D.host.g 0 * D.host.g 1 ≤ (D.host.g 0 * D.host.g 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h5 := hp.two_le
    by_contra h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have hst := GlobalTheory.Mass.StdMass.main D.host.E D.sp.cm.cmUnram D.R.k
  have h1 := (hR _ _ _ hst.1).1 hst.2.1 u
  have h2 := (h3 hp h3T (hT u).1 F0 he hz what₂ hrows).1
  have h4 : dimPi (hc := D.hcW) u = ∏ τ, vand (uS D u τ) / ∏ i ∈ range D.R.k, (i.factorial : ℝ) :=
    prod_congr rfl fun τ _ => (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS D u τ)).2
  rw [h1, h2, h4]
  change _ * (Cnt.massU D.host.E D.R.k * (Tr D u ^ D.R.k - 1) ^ D.R.f) * _ =
    Cnt.massU D.host.E D.R.k * _ * _ * _
  ring

theorem along_family_of_massRatio (hM : ∀ D : D7, UnitaryVolumeMass.stMassRatio D) :
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.FormalDegreeCompactDual → ∀ (eps : ℝ) (Fm : FamP eps) (Cg cb Cu cT CT C0 A : ℝ), 40 ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusMass.Conclusion3Family Fm → VanishingOnXAndXPlus.FamilyRowsExist Fm ∧ VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 ∧ (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) := by
  intro hE hF eps Fm Cg cb Cu cT CT C0 A hCl hR h3
  have hform : OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
      ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u := by
    obtain ⟨x0, h⟩ := hR
    refine ⟨max x0 (Fm.x1 + 1), fun x hx i hH u => ?_⟩
    have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
    exact form_of_ranks _ (h x ((le_max_left _ _).trans hx) i ⟨hH.2.1, hH.1, hH.2.2⟩) u (h3 x hx1 i u) hH.2.1
  refine ⟨fun x i => ?_, ?_, ?_, hform.mono fun _ _ _ _ h u u' hH => h hH.1 u, ⟨0, fun x _ i _ w τ => ?_⟩, hform⟩
  · intro τ w H _ _ z π hπ
    obtain ⟨g, -, hg⟩ := hπ
    exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS (Fm.D x i) w τ)).1 H _ hg
  · refine AuxiliaryNormPrimes.family_temperature_product_asymptotic_of_bessel_bound Fm Cg cb Cu cT CT C0 ?_ fun δ hδ => ?_
    · obtain ⟨x0, h0⟩ := hR
      refine ⟨x0, fun x hx i hH => ?_⟩
      have h := h0 x hx i
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hg0, -, hg1, -, -, -, -, hv, -⟩ := hH.2.1
      have hk : (5 : ℝ) ≤ (Fm.D x i).R.k := by
        have := (Fm.D x i).R.m_add_three_le_k
        have := (Fm.D x i).R.two_le_m
        exact_mod_cast (by omega : 5 ≤ (Fm.D x i).R.k)
      have hb : 1 ≤ (Fm.L x i).sc.b :=
        Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans (Fm.L x i).sc.one_lt_alt.le) _)
      have h1 : (4 : ℝ) ≤ (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 :=
        le_trans (by nlinarith) (le_self_pow₀ (by nlinarith) (by norm_num))
      exact ratio_ranks _ (hM _) (h hH) (lt_of_lt_of_le one_pos hv) (by exact_mod_cast h1.trans hg0)
        (by exact_mod_cast h1.trans hg1)
    · refine ⟨max (8 / Real.log (1 + δ)) (Fm.x1 + 1), fun x hx i _ => ?_⟩
      have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
      have h1 := (sizes_low _ (Fm.sizes x hx1 i)).1
      rw [Fm.L_x x i hx1] at h1
      exact err_le _ hδ (((le_max_left _ _).trans hx).trans h1)
  · refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    have h1 := sizes_low _ (Fm.sizes x (lt_of_lt_of_le (lt_add_one _) hx) i)
    exact tcrit_low _ _ _ _ _ _ _ _ _ _ hCl (vv_eq hE hF _ (Fm.ties x i)) h1.2 h1.1
  · exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS (Fm.D x i) w τ)).2

theorem along_family :
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.FormalDegreeCompactDual → ∀ (eps : ℝ) (Fm : FamP eps) (Cg cb Cu cT CT C0 A : ℝ), 40 ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusMass.Conclusion3Family Fm → VanishingOnXAndXPlus.FamilyRowsExist Fm ∧ VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 ∧ (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) :=
  along_family_of_massRatio _root_.GlobalTheory.MassAtRecord.massRatio_at_record

end GlobalTheory.CritLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeHsNormLeDegreeBoundRealPlace
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

private lemma hsNormSq_eq_sum_norm_sq {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (J : Wq →L[ℂ] Wp) :
    hsNormSq J = ∑ i, ‖J (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hsNormSq_le_finrank_target_mul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (J : Wq →L[ℂ] Wp) : hsNormSq J ≤ Module.finrank ℂ Wp * ‖J‖ ^ 2 := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : CompleteSpace Wq := FiniteDimensional.complete ℂ Wq

  rw [hsNormSq_eq_sum_norm_sq]
  calc ∑ i, ‖J (stdOrthonormalBasis ℂ Wq i)‖ ^ 2
        = ∑ i, ∑ j, ‖⟪(ContinuousLinearMap.adjoint J) (stdOrthonormalBasis ℂ Wp j),
            stdOrthonormalBasis ℂ Wq i⟫_ℂ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← (stdOrthonormalBasis ℂ Wp).sum_sq_norm_inner_right (J (stdOrthonormalBasis ℂ Wq i))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ContinuousLinearMap.adjoint_inner_left]
    _ = ∑ j, ‖(ContinuousLinearMap.adjoint J) (stdOrthonormalBasis ℂ Wp j)‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact (stdOrthonormalBasis ℂ Wq).sum_sq_norm_inner_left _
    _ ≤ ∑ _j : Fin (Module.finrank ℂ Wp), ‖J‖ ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hle : ‖(ContinuousLinearMap.adjoint J) (stdOrthonormalBasis ℂ Wp j)‖ ≤ ‖J‖ := by
          calc _ ≤ ‖ContinuousLinearMap.adjoint J‖ * ‖stdOrthonormalBasis ℂ Wp j‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ = ‖J‖ := by
                rw [LinearIsometryEquiv.norm_map, (stdOrthonormalBasis ℂ Wp).orthonormal.1 j, mul_one]
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = Module.finrank ℂ Wp * ‖J‖ ^ 2 := by simp

theorem sqrt_hsNormSq_amplitude_le_degBd : ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), 0 < D.host.v → 0 < θ → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → ∀ (j : ℕ) (hj : j ≤ D.R.rS) (q : ℕ) (γ : Mat D.R.k D.R.rS) (s H₁ De : ℝ) (μR νR : Measure (Mt D.R.k D.R.rS)), 1 ≤ j → j + 2 ≤ D.R.k → 16 * D.R.rS ^ 3 + 4 * D.R.rS + 2 ≤ q → 0 < s → 1 ≤ H₁ → TailBd W.z W.νS A.Φ q H₁ → TailBd W.z' W.νS' A.Φ' q H₁ → DeOK D.R.k D.R.rS W.z W.z' γ De → IsNormalFormStabilizerMeasure D.R.k D.R.rS hj W.z W.z' γ s μR → IsQuotMeas W.μG μR νR → Real.sqrt (hsNormSq (A.J νR γ)) ≤ Real.sqrt (Module.finrank ℂ W.Wp) * (((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) / s * degBd D.R.k D.R.rS j q H₁ De (Dj D.R.k D.R.rS hj W.z W.z' γ) (sgV D.R.k D.R.rS W.z W.z' γ H₁)) := by
  intro D τ w w' θ W lam A hv hθ hw hw' hW hS j hj q γ s H₁ De μR νR hj1 hjk hq hs hH hT hT' hDe hN hQ
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.AmpSides.oneSide_of_good D τ w w' θ W lam A hv hθ hw hw' hW hS
  have hκ : 0 < (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1)) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos (by linarith) _) hθ) (by positivity)
  have hb := (GlobalTheory.T.amplitude_degenerate_operatorNorm_le_realPlace D.R.k D.R.rS j hj W.z W.z' W.π W.π' _ _ W.μG W.μW W.μW' W.νS W.νS' μR νR
    A.Φ A.Φ' γ A.cN _ s H₁ De q hj1 hjk hq hκ hs hH h1 h2 hT hT' hDe hN hQ).2

  calc Real.sqrt (hsNormSq (A.J νR γ))
        ≤ Real.sqrt (Module.finrank ℂ W.Wp * ‖A.J νR γ‖ ^ 2) :=
          Real.sqrt_le_sqrt (hsNormSq_le_finrank_target_mul (A.J νR γ))
    _ = Real.sqrt (Module.finrank ℂ W.Wp) * ‖A.J νR γ‖ := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)

end GlobalTheory.Amp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefWeightedLocUncond
section
namespace GlobalTheory.Sloc.CoefWeighted

theorem coefWeightedLoc_uncond : Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc :=
  ReciprocityTheory.ChartRestriction.DS.coefWeightedLoc

end GlobalTheory.Sloc.CoefWeighted
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTermUnitaryMoveLocalTermStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTerm_unitary_move_localTerm : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Formalism.MainNotions.S.Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Formalism.MainNotions.S.Loc.HermSp M V) (r : ℕ) (g : V ≃ₗ[E] V) (t : Formalism.MainNotions.S.Loc.Term V M r), Formalism.MainNotions.S.LocNG.IsUnitary H g → H.IsTerm t → H.IsTerm (GlobalTheory.LocOver.move g t) := by
  first | exact @GlobalTheory.LocOver.isTerm_unitary_move | exact GlobalTheory.LocOver.isTerm_unitary_move | (intros; apply GlobalTheory.LocOver.isTerm_unitary_move <;> assumption)
end

