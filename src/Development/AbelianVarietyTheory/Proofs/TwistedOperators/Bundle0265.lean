module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIsotropicFlagUnipotentIffSplitChainTrivial
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SplitFlag

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)}

theorem splitVec_sub' (τ : E →ₐ[F] Fv F v) (y z : Fin V.rank → Fv F v ⊗[F] E) :
    splitVec τ (y - z) = splitVec τ y - splitVec τ z := funext fun _ => map_sub _ _ _

variable (hc : Formalism.BasicNotions.CMData F E) (τ : E →ₐ[F] Fv F v)

theorem wPart_sub_of_mem_trivOn {A B : Submodule E V.V} {g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v}
    (hg : g ∈ trivOn hc V (Fv F v) A B) {u : Fin V.rank → Fv F v} (hu : u ∈ wPart τ B) :
    (splitHom hc.sig V.gram τ g).1 *ᵥ u - u ∈ wPart τ A := by
  obtain ⟨y, hy, rfl⟩ := hu
  refine ⟨act hc V g y - y, hg.2 y hy, ?_⟩
  change splitVec τ ((matHom _ hc.sig V.gram g).1 *ᵥ y - y) = _
  rw [splitVec_sub', splitVec_matHom_mulVec]

variable (h : IsCMExt F E hc.sig) (hJ : IsHermND hc.sig V.gram)


include h hJ in
theorem mem_trivOn_of_wPart {A B : Submodule E V.V} (hAB : A ≤ B) {g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v}
    (h1 : ∀ u ∈ wPart τ B, (splitHom hc.sig V.gram τ g).1 *ᵥ u - u ∈ wPart τ A)
    (h2 : ∀ u ∈ wPart τ (perp V A), (splitHom hc.sig V.gram τ g).1 *ᵥ u - u ∈ wPart τ (perp V B))
    (h3 : ∀ u ∈ wPart τ (perp V A), ∃ u₀ ∈ wPart τ (perp V A), (splitHom hc.sig V.gram τ g).1 *ᵥ u₀ = u) :
    g ∈ trivOn hc V (Fv F v) A B := by
  refine (mem_trivOn_iff_maps hAB).2 fun y hy => ?_
  rw [mem_extSub_iff_split hc h τ] at hy ⊢
  change splitVec τ ((matHom _ hc.sig V.gram g).1 *ᵥ y - y) ∈ _ ∧
    splitVec (τ.comp hc.sig) ((matHom _ hc.sig V.gram g).1 *ᵥ y - y) ∈ _
  rw [splitVec_sub', splitVec_sub', splitVec_matHom_mulVec, splitVec_matHom_mulVec]
  refine ⟨h1 _ hy.1, ?_⟩
  rw [mem_wPart_comp_iff hc h hJ τ]
  intro u hu
  obtain ⟨u₀, hu₀, rfl⟩ := h3 u hu
  have e := (mem_wPart_comp_iff hc h hJ τ).1 hy.2 _ (h2 u₀ hu₀)
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_eq_zero] at e
  rw [sub_dotProduct, pairing_splitHom, e, sub_self]

variable (𝔉 : IsoFlag V)

theorem flagChain_step_lo (i : Fin 𝔉.k) (j : Fin (2 * 𝔉.k + 1)) (hj : (j : ℕ) = i) :
    flagChain 𝔉 τ j.succ = wPart τ (𝔉.X i.succ) ∧ flagChain 𝔉 τ j.castSucc = wPart τ (𝔉.X i.castSucc) := by
  have := i.2
  refine ⟨?_, ?_⟩
  · rw [flagChain_of_le 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (𝔉.X a)) (Fin.ext (by simp <;> omega))
  · rw [flagChain_of_le 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (𝔉.X a)) (Fin.ext (by simp <;> omega))

theorem flagChain_step_mid (j : Fin (2 * 𝔉.k + 1)) (hj : (j : ℕ) = 𝔉.k) :
    flagChain 𝔉 τ j.succ = wPart τ (perp V 𝔉.top) ∧ flagChain 𝔉 τ j.castSucc = wPart τ 𝔉.top := by
  refine ⟨?_, ?_⟩
  · rw [flagChain_of_lt 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (perp V (𝔉.X a))) (Fin.ext (by simp <;> omega))
  · rw [flagChain_of_le 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (𝔉.X a)) (Fin.ext (by simp <;> omega))

theorem flagChain_step_hi (i : Fin 𝔉.k) (j : Fin (2 * 𝔉.k + 1)) (hj : (j : ℕ) + i = 2 * 𝔉.k) :
    flagChain 𝔉 τ j.succ = wPart τ (perp V (𝔉.X i.castSucc)) ∧
      flagChain 𝔉 τ j.castSucc = wPart τ (perp V (𝔉.X i.succ)) := by
  have := i.2
  refine ⟨?_, ?_⟩
  · rw [flagChain_of_lt 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (perp V (𝔉.X a))) (Fin.ext (by simp <;> omega))
  · rw [flagChain_of_lt 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (perp V (𝔉.X a))) (Fin.ext (by simp <;> omega))

end GlobalTheory.SplitFlag


open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act) in
theorem GlobalTheory.SplitFlag.mem_unip_iff_flagChain : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)} (hc : Formalism.BasicNotions.CMData F E), IsCMExt F E hc.sig →
    IsHermND hc.sig V.gram → ∀ (τ : E →ₐ[F] Fv F v) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v),
    g ∈ 𝔉.unip hc (Fv F v) ↔ ∀ j : Fin (2 * 𝔉.k + 1), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j.succ,
      ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u - u ∈
        GlobalTheory.SplitFlag.flagChain 𝔉 τ j.castSucc := by
  intro F E _ _ _ _ _ _ V v hc h hJ τ 𝔉 g
  constructor
  · intro hg j u hu
    simp only [IsoFlag.unip, Subgroup.mem_inf, Subgroup.mem_iInf] at hg
    obtain ⟨⟨hlo, hmid⟩, hhi⟩ := hg
    have := j.2
    rcases lt_trichotomy (j : ℕ) 𝔉.k with hj | hj | hj
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_lo τ 𝔉 ⟨j, hj⟩ j rfl
      rw [e1] at hu; rw [e2]; exact GlobalTheory.SplitFlag.wPart_sub_of_mem_trivOn hc τ (hlo _) hu
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_mid τ 𝔉 j hj
      rw [e1] at hu; rw [e2]; exact GlobalTheory.SplitFlag.wPart_sub_of_mem_trivOn hc τ hmid hu
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_hi τ 𝔉 ⟨2 * 𝔉.k - j, by omega⟩ j
        (show (j : ℕ) + (2 * 𝔉.k - j) = 2 * 𝔉.k by omega)
      rw [e1] at hu; rw [e2]; exact GlobalTheory.SplitFlag.wPart_sub_of_mem_trivOn hc τ (hhi _) hu
  · intro H
    have hstab : ∀ j : Fin (2 * 𝔉.k + 2), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j,
        (splitHom hc.sig V.gram τ g).1 *ᵥ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j := by
      intro j u hu
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · rw [GlobalTheory.SplitFlag.flagChain_zero, Submodule.mem_bot] at hu ⊢
        rw [hu, Matrix.mulVec_zero]
      · have := GlobalTheory.SplitFlag.flagChain_mono 𝔉 τ (Fin.castSucc_le_succ j') (H j' u hu)
        simpa using add_mem this hu
    have hsurj : ∀ j : Fin (2 * 𝔉.k + 2), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j,
        ∃ u₀ ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j, (splitHom hc.sig V.gram τ g).1 *ᵥ u₀ = u :=
      fun j u hu => GlobalTheory.SplitFlag.exists_mulVec_eq_of_maps _ _ (hstab j) u hu
    rw [IsoFlag.mem_unip]
    refine ⟨fun i => ?_, ?_⟩
    · have := i.2
      obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_lo τ 𝔉 i ⟨i, by omega⟩ rfl
      obtain ⟨e3, e4⟩ := GlobalTheory.SplitFlag.flagChain_step_hi τ 𝔉 i ⟨2 * 𝔉.k - i, by omega⟩
        (show 2 * 𝔉.k - (i : ℕ) + i = 2 * 𝔉.k by omega)
      refine GlobalTheory.SplitFlag.mem_trivOn_of_wPart hc τ h hJ (𝔉.le_succ i) ?_ ?_ ?_
      · rw [← e1, ← e2]; exact H _
      · rw [← e3, ← e4]; exact H _
      · rw [← e3]; exact hsurj _
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_mid τ 𝔉 ⟨𝔉.k, by omega⟩ rfl
      refine GlobalTheory.SplitFlag.mem_trivOn_of_wPart hc τ h hJ 𝔉.iso ?_ ?_ ?_
      · rw [← e1, ← e2]; exact H _
      · rw [GlobalTheory.SplitFlag.perp_perp, ← e1, ← e2]; exact H _
      · rw [← e1]; exact hsurj _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemPrincGLOfCong
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Topology

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}
theorem conj_back {G : Type*} [Group G] (b g : G) : b⁻¹ * (b * g * b⁻¹) * b = g := by group

theorem mem_princGL_of_cong {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {I : Ideal (𝓞 E)} (h2 : x ∈ St β)
    {z : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hz : ∀ i j, z i j ∈ Formalism.L2.Herm.intAf F E)
    (e : (β⁻¹ * x * β).1 - 1 = Ideal.absNorm I • z) : x ∈ GlobalTheory.Grid.princGL β I := by
  obtain ⟨y, rfl⟩ := h2
  refine GlobalTheory.Grid.mem_princGL.2 ⟨y, rfl, fun i j => ?_⟩
  have e2 : β⁻¹ * frGL β y * β = intGL F E n y := conj_back β _
  rw [e2] at e
  have e3 := congrFun (congrFun e i) j
  have hmem : ((Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf F E) ∈ idS F I := by
    rw [← map_natCast (oToS F E)]
    exact Ideal.mem_map_of_mem _ (Ideal.absNorm_mem I)
  have e4 : ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) i j = ((Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf F E) * ⟨z i j, hz i j⟩ := by
    apply Subtype.ext
    refine Eq.trans ?_ (e3.trans ?_)
    · simp only [Matrix.sub_apply, Matrix.one_apply]
      split_ifs <;> rfl
    · simp [nsmul_eq_mul]
  rw [e4]
  exact Ideal.mul_mem_right _ _ hmem

theorem princ_isOpen (N : GlobalTheory.Grid.Node D) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) :
    IsOpen (((N.princ I).comap (Lev.finE N.V) : Subgroup (GA D N.V)) : Set (GA D N.V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig N.V.gram
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig N.V.gram
  have hf : Continuous (finHom N.V) := (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
  have hN : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 hI
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ N.V N.β ∅,
    GlobalTheory.FunObj.eventually_cong_mat N.β hN hf (map_one _)] with κ ⟨h1, h2, _⟩ ⟨z, hz, e⟩
  exact ⟨h1, mem_princGL_of_cong h2 hz e⟩

theorem princ_isCompact (N : GlobalTheory.Grid.Node D) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) :
    IsCompact ((Lev.levA N.V (N.princ I) : Subgroup (GA D N.V)) : Set (GA D N.V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig N.V.gram
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact N.V N.β
  refine hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC N.V).inter
    (Subgroup.isClosed_of_isOpen _ (princ_isOpen N hI))) fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
  exact hCm k hk1 (GlobalTheory.Grid.princGL_top N.β ▸ GlobalTheory.Grid.princGL_mono N.β le_top hk2.2)

theorem exists_isMeasFD (V : HSp D) (hV : V.SigOK) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (ho : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)))
    (hc : IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V))) : ∃ μ 𝓕, Lev.IsMeasFD V K μ 𝓕 := by
  choose m hm using GlobalTheory.MinfMeasure.exists_isMinf
  obtain ⟨μ, hμ⟩ := GlobalTheory.LevelMeasure.exists_isMeasLevW D V hV K ho hc (fun _ m => Lev.IsMinf m) (fun _ => m _ _)
    (fun _ => (hm _ _).1) (fun _ => hm _ _) fun _ _ h => GlobalTheory.LevelMeasure.isMinf_unique (hm _ _) h
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ.1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

theorem exists_measDat (N : GlobalTheory.Grid.Node D) (hs : N.V.SigOK) (df : Prop) (hdf : df → ∀ τ, (N.V.sig τ).2 = 0)
    {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) : ∃ m : N.MeasDat, m.Is df (N.princ I) := by
  have ho := princ_isOpen N hI
  have hc := princ_isCompact N hI
  by_cases h : df
  · obtain ⟨μ, 𝓕, e⟩ := GlobalTheory.FunObj.exists_meas N.V hs (hdf h) (N.princ I) ⟨ho, hc⟩
    rw [if_pos rfl] at e
    exact ⟨⟨μ, 𝓕⟩, by unfold GlobalTheory.Grid.Node.MeasDat.Is; exact ⟨fun _ => e, fun hn => absurd h hn⟩⟩
  · obtain ⟨μ, 𝓕, e⟩ := exists_isMeasFD N.V hs _ ho hc
    exact ⟨⟨μ, 𝓕⟩, by unfold GlobalTheory.Grid.Node.MeasDat.Is; exact ⟨fun h' => absurd h' h, fun _ => e⟩⟩

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem exists_isMeas (G : GlobalTheory.Grid.GridPre R) (hS : G.IsSpaces) :
    ∃ m00 mV mP mX, (withMeas G m00 mV mP mX).IsMeas := by
  have hlvl : G.lvl R ≠ ⊥ := G.toPlaceDat.ideal_ne_bot R.Pg
  have htop : (⊤ : Ideal (𝓞 D.host.E)) ≠ ⊥ := top_ne_bot
  obtain ⟨m00, h00⟩ := exists_measDat (G.V 0 0) (D.sp.Y_sig 0) False (fun h => h.elim) hlvl
  have hV : ∀ i j, ∃ m : (G.nV i j).MeasDat, i + 1 ≤ D.R.m → j ≤ D.R.m →
      m.Is (if j = 0 then False else D.R.m - 1 ≤ j) ((G.nV i j).princ (if j = 0 then G.lvl R else ⊤)) := by
    intro i j
    by_cases h : i + 1 ≤ D.R.m ∧ j ≤ D.R.m
    · have hN := hS.vert i j h.1 h.2
      obtain ⟨m, hm⟩ := exists_measDat (G.nV i j) hN.sigOK (if j = 0 then False else D.R.m - 1 ≤ j)
        (fun hd τ => by
          rw [hN.sig τ]
          show (D.R.m - j) / 2 = 0
          by_cases hj : j = 0
          · rw [if_pos hj] at hd; exact hd.elim
          · rw [if_neg hj] at hd; omega)
        (I := if j = 0 then G.lvl R else ⊤) (by split_ifs; exacts [hlvl, htop])
      exact ⟨m, fun _ _ => hm⟩
    · exact ⟨⟨0, ∅⟩, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  have hP : ∀ i, ∃ m : (G.P i).MeasDat, i ≤ D.R.m → m.Is (i = D.R.m) ((G.P i).princ (G.lvl R)) := by
    intro i
    by_cases h : i ≤ D.R.m
    · have hN := hS.P i h
      obtain ⟨m, hm⟩ := exists_measDat (G.P i) hN.sigOK (i = D.R.m)
        (fun hd τ => by
          rw [hN.sig τ]
          show (D.R.m - i + 1) / 2 = 0
          omega) hlvl
      exact ⟨m, fun _ => hm⟩
    · exact ⟨⟨0, ∅⟩, fun h1 => absurd h1 h⟩
  have hX : ∀ j, ∃ m : (G.nX j).MeasDat, j + 1 ≤ D.R.m → m.Is True ((G.nX j).princ ⊤) := by
    intro j
    by_cases h : j + 1 ≤ D.R.m
    · have hN := hS.X j h
      obtain ⟨m, hm⟩ := exists_measDat (G.nX j) hN.sigOK True
        (fun _ τ => by
          rw [hN.sig τ]) htop
      exact ⟨m, fun _ => hm⟩
    · exact ⟨⟨0, ∅⟩, fun h1 => absurd h1 h⟩
  choose mV hmV using hV
  choose mP hmP using hP
  choose mX hmX using hX
  refine ⟨m00, mV, mP, mX, ⟨fun i hi => ?_, fun i j hi hj => ?_, fun i hi => hmP i hi, fun j hj => hmX j hj⟩⟩
  · cases i with
    | zero => exact h00
    | succ i =>
      have := hmV i 0 hi (Nat.zero_le _)
      rw [if_pos rfl, if_pos rfl] at this
      exact this
  · have := hmV i (j + 1) hi hj
    rw [if_neg (Nat.succ_ne_zero j), if_neg (Nat.succ_ne_zero j)] at this
    exact this

end GlobalTheory.GridJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedFormTorusTranslateVacuumValue
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.SphTheta.TorusVac

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def lmulI {n' n : ℕ} (A : Matrix (Fin n') (Fin n') L) : Matrix (Fin n') (Fin n) L →ₗ[intL L] Matrix (Fin n') (Fin n) L where
  toFun x := A * x
  map_add' := Matrix.mul_add A
  map_smul' r x := Matrix.mul_smul A r x

def ex (n' : ℕ) (k : Fin (n' / 2)) (i : Fin n') : ℤ :=
  if i = lo n' k then 1 else if i = (lo n' k).rev then -1 else 0

theorem tMat_single (ϖ : L) (n' : ℕ) (k : Fin (n' / 2)) :
    tMat ϖ n' (n' / 2) (Pi.single k 1) = Matrix.diagonal (fun i => ϖ ^ ex n' k i) := by
  unfold tMat
  congr 1
  funext i
  have hk := k.2
  have hi := i.2
  simp only [ex, Pi.single_apply, lo, Fin.ext_iff, Fin.val_rev]
  split_ifs <;> simp_all <;> omega

variable {σ : L →+* L} {δ : L} {ψ : AddChar L ℂ} {n n' : ℕ}

theorem pairing_unitary (h : GU σ n') (x y : Matrix (Fin n') (Fin n) L) :
    pairing σ δ ψ (h.1.1 * x) (h.1.1 * y) = pairing σ δ ψ x y := by
  have hu : cT σ h.1.1 * antiJ L n' * h.1.1 = antiJ L n' := h.2
  have hl : locH σ δ (antiG L n) (antiG L n') (h.1.1 * x) (h.1.1 * y) = locH σ δ (antiG L n) (antiG L n') x y := by
    unfold locH
    congr 1
    have e1 : ((h.1.1 * y).map σ)ᵀ = (y.map σ)ᵀ * cT σ h.1.1 := by
      rw [Matrix.map_mul, Matrix.transpose_mul]; rfl
    have e2 : ((antiG L n' : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) = antiJ L n' := rfl
    rw [e1, e2]
    congr 1
    calc _ = (((antiG L n)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (y.map σ)ᵀ * (cT σ h.1.1 * antiJ L n' * h.1.1) * x := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu]
  have e3 : ∀ a b : Matrix (Fin n') (Fin n) L, pairing σ δ ψ a b =
      ψ (locH σ δ (antiG L n) (antiG L n') a b + σ (locH σ δ (antiG L n) (antiG L n') a b)) := by
    intro a b; rw [locH_antiG]; rfl
  rw [e3, e3, hl]

theorem mul_inv_val (t : GU σ n') : t.1.1 * (t⁻¹).1.1 = 1 := by
  rw [show t.1.1 * (t⁻¹).1.1 = (t * t⁻¹).1.1 from rfl, mul_inv_cancel]; rfl

theorem selfDual_map (t : GU σ n') {A : Submodule (intL L) (Matrix (Fin n') (Fin n) L)}
    (hA : SelfDual (pairing σ δ ψ) A) : SelfDual (pairing σ δ ψ) (A.map (lmulI t.1.1)) := by
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩ _ ⟨b, hb, rfl⟩
    show pairing σ δ ψ (t.1.1 * y) (t.1.1 * b) = 1
    rw [pairing_unitary]
    exact (hA y).1 hy b hb
  · intro H
    have hy : (t⁻¹).1.1 * x ∈ A := by
      refine (hA _).2 fun b hb => ?_
      rw [← pairing_unitary t, ← Matrix.mul_assoc, mul_inv_val, Matrix.one_mul]
      exact H _ ⟨b, hb, rfl⟩
    refine ⟨_, hy, ?_⟩
    show t.1.1 * ((t⁻¹).1.1 * x) = x
    rw [← Matrix.mul_assoc, mul_inv_val, Matrix.one_mul]

theorem idx_translate_ne {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (t : GU σ n') (d : Fin n' → ℤ)
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) :
    idx (intMat L (Fin n') (Fin n)) ((intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) ≠ 0 := by
  have h := GlobalTheory.LatIdx.relIndex_intMat_translate ϖ σ q hU n' n d t ht 1 (one_mem _) 1 (one_mem _)
  simp only [one_mul, mul_one] at h
  have e1 : (intMat L (Fin n') (Fin n)).toAddSubgroup = GlobalTheory.InertHomIdx.intMat L n' n :=
    AddSubgroup.ext fun _ => Iff.rfl
  have e2 : ((intMat L (Fin n') (Fin n)).map (lmulI (n := n) t.1.1)).toAddSubgroup =
      AddSubgroup.map (GlobalTheory.InertHomIdx.lmul t.1.1) (GlobalTheory.InertHomIdx.intMat L n' n) :=
    AddSubgroup.ext fun _ => Iff.rfl
  unfold idx
  rw [e1, e2, h]
  exact pow_ne_zero _ (pow_ne_zero _ (by have := hU.2.2.2.2.2.1; omega))

theorem mem_of_mixLat {ϖ : L} (hϖ : Valued.v ϖ ≤ 1) (k : Fin (n' / 2)) (t : GU σ n')
    (hT : t.1.1 = Matrix.diagonal fun i => ϖ ^ ex n' k i) {x a : Matrix (Fin n') (Fin n) L}
    (hx : x ∈ (intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) (ha : a ∈ mixLat L n' n)
    (hxa : x - a ∈ intMat L (Fin n') (Fin n)) : x ∈ intMat L (Fin n') (Fin n) := by
  obtain ⟨y, hy, rfl⟩ := hx
  intro r c
  by_cases hr : r = (lo n' k).rev
  · have hk := k.2
    have h0 : a r c = 0 := (ha r c).1 (Or.inl (by subst hr; simp only [lo, Fin.val_rev]; omega))
    have := hxa r c
    rwa [Matrix.sub_apply, h0, sub_zero] at this
  · show (t.1.1 * y) r c ∈ intL L
    rw [hT, Matrix.diagonal_mul]
    have hp : ϖ ^ ex n' k r ∈ intL L := by
      have he : ex n' k r = 1 ∨ ex n' k r = 0 := by
        unfold ex; split_ifs <;> simp_all
      rcases he with he | he <;> rw [he]
      · simpa using mem_intL.2 hϖ
      · simpa using one_mem (intL L)
    exact mul_mem hp (hy r c)

end GlobalTheory.SphTheta.TorusVac


open GlobalTheory.SphTheta.TorusVac in
theorem GlobalTheory.SphTheta.mixed_torus_value : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n ρ (ω.comp (MonoidHom.inr _ _)) s → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 → (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) → ∀ (k : Fin (n' / 2)) (t : GU σ n'), t.1.1 = tMat ϖ n' (n' / 2) (Pi.single k 1) → ℓ (ω (1, t) s) = (-1) ^ n * (q : ℂ) ^ (-(n : ℤ)) := by
  intro L _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS hC ℓ hℓs hℓmix hℓzero k t ht
  have hU := hS.1.unr
  have hH := hS.isHeis
  have hΛ := hS.selfDual
  have hϖle : Valued.v ϖ ≤ 1 := by
    rw [hU.2.2.2.1]; exact_mod_cast (by decide : (Multiplicative.ofAdd (-1:ℤ)) ≤ 1)
  have hT : t.1.1 = Matrix.diagonal (fun i => ϖ ^ ex n' k i) := ht.trans (tMat_single ϖ n' k)
  have hΛ' := selfDual_map (n := n) (δ := δ) (ψ := ψ) t hΛ
  have hidx := idx_translate_ne (n := n) hU t _ hT
  obtain ⟨e, he1, heinv⟩ := _root_.GlobalTheory.SphTheta.exists_linearForm_invariant_isotropic_vacuum hH _ hΛ s hS.2.1 hS.fixes hS.2.2.2 _ (fun a ha b hb => hH.iso hΛ ha hb)
  have hv : Fixes ρ ((intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) (ω (1, t) s) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := congrArg (fun F : Module.End ℂ M => F s) (hS.1.norm 1 t y)
    simp only [Module.End.mul_apply] at h1
    rw [hS.fixes y hy] at h1
    simp at h1
    exact h1.symm
  have hsum : ℓ (sumOp ρ (intMat L (Fin n') (Fin n)) ((intMat L (Fin n') (Fin n)).map (lmulI t.1.1)) s) = 1 := by
    obtain ⟨N, f, hf, hu⟩ := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le hH _ _ hΛ').2.1 hidx).1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le hH _ _ hΛ').1 s hS.fixes (Fin N) f hf hu).1, map_sum]
    obtain ⟨i0, hi0, huniq⟩ := hu 0 (zero_mem _)
    have key : ∀ i, ℓ (ρ (f i) s) = if i = i0 then 1 else 0 := by
      intro i
      by_cases hfi : f i ∈ intMat L (Fin n') (Fin n)
      · have : i = i0 := huniq i (by show 0 - f i ∈ _; rw [zero_sub]; exact neg_mem hfi)
        rw [if_pos this, hS.fixes _ hfi, hℓs]
      · have hne : i ≠ i0 := by
          rintro rfl
          apply hfi
          have := neg_mem hi0
          rwa [zero_sub, neg_neg] at this
        rw [if_neg hne]
        apply hℓzero
        rintro ⟨a, ha, hxa⟩
        exact hfi (mem_of_mixLat hϖle k t hT (hf i) ha hxa)
    simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  obtain ⟨hd, hint, hord⟩ := _root_.GlobalTheory.CayleyTorus.cayley_torus_inv L ϖ σ q hU hS.v_two n' k t ht
  have hev := hC e heinv t⁻¹ hd hint
  rw [inv_inv, hord, he1, mul_one] at hev
  have hco := (_root_.GlobalTheory.SphTheta.sumOp_vacuum_lift hH _ hΛ s hS.2.1 hS.fixes hS.2.2.2 _ hΛ' hidx).2 e he1 heinv _ hv
  rw [hco, map_smul, hsum, smul_eq_mul, mul_one]
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply] at hev
  rw [hev, _root_.zpow_neg, zpow_one, mul_inv, _root_.zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeVectorHeckeEigenvalueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_vector_hecke_eigenvalue : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → ∀ (z : ℂˣ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∀ c : (Fin r → ℤ) → ℂ, (∀ d, heckeVec ρ (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) (T d)) x = c d • x) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => (z : ℂ) ^ (∑ i, d.1 i) * c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac (B.map (z * ·)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B.map fun β => (z * β)⁻¹) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  first | exact @GlobalTheory.FinZeta.GLTwist.hasSum_twisted_hecke_eigenvalues | exact GlobalTheory.FinZeta.GLTwist.hasSum_twisted_hecke_eigenvalues | (intros; apply GlobalTheory.FinZeta.GLTwist.hasSum_twisted_hecke_eigenvalues <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicIndepCovolumeMeasure
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerRestrict

theorem res_indep_covol : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (d : GlobalTheory.MixModel.HypDec V V' r), d.e = C → d.i₀ = B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ (μ μ' : Measure (Mx D W.rank r)) (𝓨 𝓨' : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ' 𝓨' → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ' 𝓨' f = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs d _ _ ψ f hf μ μ' 𝓨 𝓨' h h'
  funext x
  exact GlobalTheory.MixModel.covolOne_integral_eq h h' (fun y => f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x))
    (fun γ hγ y => periodic_iso hs hf x γ hγ y)

end GlobalTheory.TowerRestrict
end

