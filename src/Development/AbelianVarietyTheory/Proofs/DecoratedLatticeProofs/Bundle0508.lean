module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0505
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0429

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumSplitPlaceCombinationMulLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod


set_option maxHeartbeats 1000000 in
theorem ratDatum_comb_place : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → DenseRange p.pr → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → IsIdemSum (e + p.e) (@insert _ _ (@Finset.instInsert _ (Classical.decEq _)) PP P) → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank → (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank → ∀ (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (Ξk : Matrix Y Y' k → ℂ), Ξk ∈ SB (Matrix Y Y' k) → ∀ c, p.IsCombAt ψ FS FT c Ξk → ∀ f₀ f, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsRatDatum ψ S T e Ξ f₀ f → IsRatDatum ψ S T (e + p.e) (fun γ => Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) f₀ (comb ψ S T c f) := by
  intro D k _ _ _ _ p ψ hψ hdense S T Y Y' _ _ _ _ FS FT P PP e hPP hIdemAt hE hE' hstd ΛS ΛT hS hT hΛS hΛT Ξ Ξk hΞk c hc
    f₀ f hf₀ hvac hf
  have hL : stdHom S T = latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    rw [hΛS, hΛT]
  have hf₁ := hf
  obtain ⟨Φ, hΦSB, hΦrat, -⟩ := hf₁
  have he1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have he2 : (e + p.e) * (e + p.e) = e + p.e := GlobalTheory.PlaceDatum.idemSum_mul_self hE'
  have hpe2 : p.e * p.e = p.e := p.split.1
  have horth : e * p.e = 0 := by
    have h2 : incA D 2 * (e * p.e) = 0 := by
      rw [map_ofNat]
      linear_combination he2 - he1 - hpe2
    have hu : incA D (1 / 2) * incA D 2 = 1 := by
      rw [← map_mul]
      norm_num
    calc e * p.e = incA D (1 / 2) * (incA D 2 * (e * p.e)) := by rw [← mul_assoc, hu, one_mul]
      _ = 0 := by rw [h2, mul_zero]
  have hstabp : ∀ u ∈ stdHom S T, u.map (fun a => p.e * a) ∈ stdHom S T := fun u hu => by
    have := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ p.e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hpe2])) u hu
    convert this using 1
    ext i j
    rfl
  have hsb := GlobalTheory.LocMod.Place.isSBHalf_tensorAt D k p S T Y Y' FS FT e horth hstd hstabp Φ hΦSB Ξk hΞk
  have hpi1 : p.π p.e = 1 := by
    have h := p.ι_π 1
    rw [map_one, mul_one] at h
    rw [← h, p.π_ι]
  have hπe : p.π e = 0 := by
    have := congrArg p.π horth
    rwa [map_mul, hpi1, mul_one, map_zero] at this
  have hud : ∀ t : WO S T, p.up FS FT (p.down FS FT t) = t.map (fun x => p.e * x) := fun t => by
    unfold Place.up Place.down
    have hM : FT.β * (FT.γ * (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ =
        (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
    rw [hM]
    ext i j
    simp only [Matrix.map_apply, p.ι_π]
  have hrat : ∀ γ, p.tensorAt FS FT Φ Ξk (γ.map fun a => (e + p.e) * incA D a) = Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β) :=
    fun γ => by
    have hd : p.down FS FT (γ.map fun a => (e + p.e) * incA D a) = FT.γ * γ.map p.pr * FS.β := by
      unfold Place.down
      congr 2
      ext i j
      simp only [Matrix.map_apply, map_mul, map_add (f := _), hπe, hpi1, zero_add, one_mul, Place.pr]
    have hs : ((γ.map fun a => (e + p.e) * incA D a : WO S T) - p.up FS FT (p.down FS FT (γ.map fun a => (e + p.e) * incA D a)) : WO S T) =
        (γ.map fun a => e * incA D a : WO S T) := by
      rw [hud]
      ext i j
      simp only [Matrix.sub_apply, Matrix.map_apply]
      have h2 : p.e * e = 0 := by rw [mul_comm]; exact horth
      linear_combination (-(incA D (γ i j))) * h2 + (-(incA D (γ i j))) * hpe2
    simp only [Place.tensorAt]
    rw [hs, hd, hΦrat]
  have hvac' : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀ := by
    rw [← hL]; exact hvac
  have hex := (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hψ S T ΛS ΛT hS hT _ (e + p.e) hE' f₀ hf₀ hvac').1
  have hsb' : IsSBHalf (e + p.e) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (p.tensorAt FS FT Φ Ξk) := by
    rw [← hL]; exact hsb
  obtain ⟨f', hf'⟩ := GlobalTheory.PlaceVec.exists_isThetaAt hψ hS hT he2 (GlobalTheory.PlaceDatum.infPart_idemSum hE') hex hsb'
  have hR : IsRatDatum ψ S T (e + p.e) (fun γ => Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) f₀ f' :=
    ⟨p.tensorAt FS FT Φ Ξk, hsb, hrat, by rw [hL]; exact hf'⟩
  have key := _root_.GlobalTheory.LocMod.ratDatum_factor D k p ψ hψ hdense S T Y Y' FS FT P PP e hPP hIdemAt hE hE' hstd Ξ _ Ξk hΞk (fun _ => rfl) c hc
    f₀ f f' hf₀ hvac hf hR
  rw [← key]
  exact hR

end GlobalTheory.LocMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFiniteIntegralsDoubleStepValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ValFin

variable {D : D7}

theorem isThetaFunO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T 0 :=
  ⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun _ _ _ => by funext w; simp [heisO]⟩, continuous_const,
    fun _ _ _ _ _ => by simp only [Pi.zero_apply]; exact contDiff_const⟩

theorem isLatVac_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) :
    IsLatVac (heisO ψ S T) Λ 0 :=
  ⟨fun _ _ => by funext w; simp [heisO], fun _ _ _ _ _ => by funext w; simp [heisO]⟩

theorem isReal_zero (c : Comm D) (j : ℕ) : c.IsReal j 0 := by
  refine ⟨⟨continuous_const, fun v => ⟨isThetaFunO_zero _ _ _, isLatVac_zero _ _ _ _⟩,
    fun u => ⟨isThetaFunO_zero _ _ _, isLatVac_zero _ _ _ _⟩⟩, ?_⟩
  intro n L L' _ _ _ _ u v
  simp only [Pi.zero_apply]
  exact contDiff_const

theorem isAutFun_rTrans {V : HSp D} (x : GA D V) {φ : GA D V → ℂ} (h : IsAutFun V φ) :
    IsAutFun V (rTrans x φ) := by
  obtain ⟨U, hU, hUφ⟩ := h.level
  refine ⟨fun γ hγ g => ?_, ⟨U.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, fun k hk hkf g => ?_⟩, ?_⟩
  · simp only [rTrans, mul_assoc]; exact h.left γ hγ (g * x)
  · have hc : Continuous fun k : GA D V => x⁻¹ * k * x := by fun_prop
    exact hU.preimage hc
  · have hk' : x⁻¹ * k * x ∈ U := by simpa [MulAut.conj_apply] using hk
    have hf : x⁻¹ * k * x ∈ GfC V := by
      unfold GfC at hkf ⊢
      rw [MonoidHom.mem_ker] at hkf ⊢
      simp [hkf]
    have e : g * k * x = g * x * (x⁻¹ * k * x) := by group
    simp only [rTrans]
    rw [e, hUφ _ hk' hf]
  · exact h.cont.comp (continuous_mul_const x)

theorem trc_mapDomain {V : HSp D} (ε : GA D V →₀ ℂ) (b : GA D V) (f : GA D V → ℂ) :
    trc (ε.mapDomain (· * b)) f = trc ε (rTrans b f) := by
  unfold trc
  change (ε.mapDomain (· * b)).sum (fun g c => c • rTrans g f) = ε.sum (fun g c => c • rTrans g (rTrans b f))
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 1
  funext z
  simp [rTrans, mul_assoc]

end GlobalTheory.ValFin

namespace GlobalTheory.ValFin

variable {D : D7}

theorem vac_of_all {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (Q : Pl D → Prop) {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT Q f := by
  have key := (_root_.GlobalTheory.DisjComb.main D ψ hstd S T Q (fun p => ¬ Q p) (fun p hp hn => hn hp)).2.2.2.2 LS LT f hS hT
  have e : (fun p => Q p ∨ ¬ Q p) = fun _ => True := funext fun p => propext ⟨fun _ => trivial, fun _ => em _⟩
  rw [e] at key
  exact (key.1 hf).1

theorem ctr_indep (c : Comm D) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (s₁ s₁' : StepBF c.ψ (c.B j (σ + 1) h) (c.J j (σ + 1) h))
    (s₂ s₂' : StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)))
    (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) (c.V (j + 1 + 1)) → ℂ)
    (h₁ : IsThetaFunO c.ψ _ _ Ψ₁) (h₂ : IsThetaFunO c.ψ _ _ Ψ₂) :
    c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂ = c.ctr j σ h s₁' s₂' Ψ₁ Ψ₂ := by
  unfold Comm.ctr
  rw [(_root_.GlobalTheory.FlatIndep.flat_indep D c.ψ).1 _ _ _ s₁ s₁' Ψ₁ h₁, (_root_.GlobalTheory.FlatIndep.flat_indep D c.ψ).2 _ _ _ s₂ s₂' Ψ₂ h₂]

theorem valX : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)), c.Is → v.Is →
    (∀ s, (t s).Is) → (∀ s, PlaceLaws v (w s)) → ContrLaw D → FlatLaw D → BiAct D → ValX t := by
  intro D c v 𝒯 t w hc hv ht hL hContr hFlat hBi
  intro j σ h P₁ P₂ a ha a' ha'
  have hj1 : j + 1 < D.R.m := by omega
  have hj2 : j + 1 + 1 < D.R.m := by omega
  have hV₁ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) (v.Ψ j P₁ 1 a) :=
    hv.Ψ j hj1 P₁ 1 (one_mem _) a ha
  have hV₂ : Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) (v.Ψ (j + 1) P₂ a a') :=
    hv.Ψ (j + 1) hj2 P₂ a ha a' ha'
  by_cases hT : Nonempty 𝒯
  swap
  · exact ⟨0, isReal_zero c j, fun s => (hT ⟨s⟩).elim⟩
  obtain ⟨s₀⟩ := hT
  refine ⟨(v.op j).app c.ψ (c.ctr j σ h ((t s₀).sBF j (σ + 1) h) ((t s₀).sFB j σ h) (v.Ψ j P₁ 1 a) (v.Ψ (j + 1) P₂ a a')),
    ((GlobalTheory.T.seeSaw_commonRealDatum_biTheta_vacuum_contraction D c v (t s₀) (w s₀) hc hv (ht s₀) (hL s₀).vac (hL s₀).tl hFlat).1 j σ h _ _ hV₁ hV₂).2, ?_⟩
  intro s ψ hψ y G x
  have hLs := hL s
  have hF := hLs.form
  have hj2m : j + 2 ≤ D.R.m := by omega
  have hφR : ∀ α, (t s).rd j α ψ y ∈ v.RamAd j := fun α => (hF.rd j hj2m ψ hψ α y).1
  have hφX : ∀ α, (t s).rd j α ψ y ∈ (w s).FX j α := fun α => (hF.rd j hj2m ψ hψ α y).2.1
  have hφS : ∀ α, (t s).rd j α ((t s).S j ψ) y = v.Sad j ((t s).rd j α ψ y) := fun α => (hF.rd j hj2m ψ hψ α y).2.2
  have hφA : ∀ α, IsContAut _ ((t s).rd j α ψ y) := fun α => (hv.ram j _ (hφR α)).1
  have hFaut : IsAutFun _ (G.1 x) := by
    obtain ⟨J, χ, hJ⟩ := (ht s).CC (j + 1 + 1) hj2
    exact (GlobalTheory.PairLift.LowAllPf.multT_apply_smooth_cusp c.θ (c.M (j + 1 + 1)) J χ G.1 (hJ G.2) x).1.toIsAutFun
  have hfaut : IsAutFun _ (rTrans (a' * v.b (j + 1 + 1)) (G.1 x)) := isAutFun_rTrans _ hFaut
  have hfY : rTrans (a' * v.b (j + 1 + 1)) (G.1 x) ∈ (w s).FY (j + 1 + 1) := (hF.row (j + 1 + 1) hj2 G x a' ha').1
  obtain ⟨ρ₁, μ₁, hn₁⟩ := _root_.GlobalTheory.SeeSaw.normAt_exists D (c.V (j + 1)) (jacGrp (c.jac j (σ + 1) h).d) (GlobalTheory.jacGrp_isClosed _ _ _ _ _)
    (v.N (j + 1)) (hv.sd (j + 1) hj1) (w s).Q
  obtain ⟨ρ₂, μ₂, hn₂⟩ := _root_.GlobalTheory.SeeSaw.normAt_exists D (c.V (j + 1 + 1))
    (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o)
    (GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ _ _) (v.N (j + 1 + 1)) (hv.sd (j + 1 + 1) hj2) (w s).Q
  have hdisj : ∀ p, p ∈ v.gP → ¬ p ∈ (w s).Q := fun p hp hq => Finset.disjoint_left.mp hF.disjG hq hp
  have K₁ := _root_.GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (· ∈ v.gP) (· ∈ (w s).Q) hdisj
  have K₂ := _root_.GlobalTheory.DisjComb.main D c.ψ hc.std (c.V (j + 1)) (c.V (j + 1 + 1)) (· ∈ v.gP) (· ∈ (w s).Q) hdisj
  have hVQ₁ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ (w s).Q) (comb c.ψ _ _ (v.eG j) (v.Ψ j P₁ 1 a)) :=
    (K₁.2.1 (v.eG j) (hv.atG j).1).2 _ _ _
      (vac_of_all hc.std (hv.sd j (by omega)) (hv.sd (j + 1) hj1) _ hV₁)
  have hVQ₂ : Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ (w s).Q) (comb c.ψ _ _ (v.eG (j + 1)) (v.Ψ (j + 1) P₂ a a')) :=
    (K₂.2.1 (v.eG (j + 1)) (hv.atG (j + 1)).1).2 _ _ _
      (vac_of_all hc.std (hv.sd (j + 1) hj1) (hv.sd (j + 1 + 1) hj2) _ hV₂)
  have hQ := hLs.ql j σ h ρ₁ μ₁ ρ₂ μ₂ hn₁ hn₂ _ _ hVQ₁ hVQ₂ (fun α => (t s).rd j α ψ y)
    (fun α => ⟨hφA α, hφX α⟩) _ hfaut hfY
  have hc₁ := K₁.1 (v.eG j) ((w s).eQ j) (hv.atG j).1 (hF.atQ j).1 (v.Ψ j P₁ 1 a)
  have hc₂ := K₂.1 (v.eG (j + 1)) ((w s).eQ (j + 1)) (hv.atG (j + 1)).1 (hF.atQ (j + 1)).1 (v.Ψ (j + 1) P₂ a a')
  rw [← hc₁, ← hc₂] at hQ
  have hcell := GlobalTheory.T.seeSawDoubleStep_finiteIntegral_collapse_twistPlaces D c v (t s) (w s) hc hv (ht s) hF hLs.weil hLs.off hLs.gs hLs.qfin hContr hFlat j σ h
    ρ₁ μ₁ ρ₂ μ₂ hn₁ hn₂ _ _ hV₁ hV₂ (fun α => (t s).rd j α ψ y) hφR G x a' ha' _ rfl _ hQ
  have hmove := _root_.GlobalTheory.VMove.seeSaw_iteratedIntegrand_vacuumForm_base_points_alt D c v (t s) (w s) hc hv (ht s) hF j σ h P₁ P₂ a ha a' ha' (fun α => (t s).rd j α ψ y)
    (G.1 x) _ _ _ _ rfl rfl rfl hcell
  convert hmove using 1
  have hrhs := GlobalTheory.T.seeSaw_unfoldedData_eq_kernelData_at_level D c v (t s) (w s) hc hv (ht s) hF hLs.gv hLs.tl hFlat hBi j σ h _ _ hV₁ hV₂
    (fun α => (t s).rd j α ψ y) hφR
  have hct := ctr_indep c j σ h ((t s).sBF j (σ + 1) h) ((t s₀).sBF j (σ + 1) h) ((t s).sFB j σ h) ((t s₀).sFB j σ h)
    _ _ hV₁.1 hV₂.1
  rw [hct] at hrhs
  beta_reduce at hrhs
  have hper : ∀ (k : ℂ) φ' f', (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (k • φ') f' =
      k * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ φ' f' := by
    intro k φ' f'
    have := (GlobalTheory.HandHom.hand_hom D c.ψ σ (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))
      ((t s).sBF j (σ + 1) h) ((t s).sFB j σ h) (c.lnk j σ h) (c.vL j σ h) 0).2.2 k 1 φ' f'
    rwa [one_smul, mul_one] at this
  have htwo : (fun α => (t s).rd j α ((t s).S j ψ) y) = fun α => v.Sad j ((t s).rd j α ψ y) := funext hφS
  have hcomm : v.b (j + 1 + 1) * a' = a' * v.b (j + 1 + 1) :=
    GlobalTheory.FinTranslate.comm_fin_real _ (hv.b (j + 1 + 1)) ha'
  have htrc : ∀ β, trc ((t s).e (j + 1 + 1) β) (rTrans a' (G.1 x)) =
      trc ((w s).ε (j + 1 + 1) β) (rTrans (a' * v.b (j + 1 + 1)) (G.1 x)) := by
    intro β
    rw [(hF.e (j + 1 + 1) β).1, trc_mapDomain]
    congr 1
    funext g
    simp [rTrans, mul_assoc, hcomm]
  rw [hLs.cv.1 j σ h]
  unfold Tup.perF
  rw [htwo]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [hrhs β, hper, htrc β]
  ring

end GlobalTheory.ValFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawIteratedIntegralLawLastStepsOfLocalFactori
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QLastPf

theorem heisO_smul' {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (a : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (a • f) = a • heisO ψ S T u f := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem comb_smul_left {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : ℂ) (e : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • e) f = a • comb ψ S T e f := by
  by_cases ha : a = 0
  · simp [comb, ha]
  · rw [comb, comb, Finsupp.support_smul_eq ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finsupp.smul_apply, smul_smul, smul_eq_mul]

theorem comb_smul_right {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : ℂ) (e : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T e (a • f) = a • comb ψ S T e f := by
  rw [comb, comb, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [heisO_smul', smul_comm]

theorem biComb_smul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (a b : ℂ) (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' (a • e) (b • e') C = (a * b) • biComb ψ A S A' e e' C := by
  funext u v
  simp only [biComb, comb_smul_left]
  have e1 : (fun u' => (b • comb ψ S A' e' (C u')) v) = b • fun u' => comb ψ S A' e' (C u') v := by
    funext u'; simp
  rw [e1, comb_smul_right]
  simp only [Pi.smul_apply, smul_eq_mul, biComb]
  ring

theorem block_smul₂ {D : D7} (c : Comm D) (j : ℕ) (oma : Om (c.X j) (c.X (j + 1))) (omb : Om (c.X (j + 1)) (c.X (j + 1 + 1)))
    (φ : GA D (c.X j) → ℂ) (a : ℂ) (C : WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ) :
    c.bl j oma omb φ (a • C) = a • c.bl j oma omb φ C := by
  funext h₂
  simp only [Comm.bl, biLift, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext h₁
  rw [← integral_const_mul]
  congr 1; funext h₀
  have e1 : ∀ v, (fun u => a * C u v) = a • fun u => C u v := fun v => by funext u; simp
  simp_rw [e1, map_smul]
  have e2 : (fun v => (a • oma (h₀, h₁) (fun u => C u v)) 0) = a • fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v; simp
  rw [e2, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem alg_of_core : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPin v w → ∀ j (h : j + 2 * 0 + 2 = D.R.m) Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ w.Q) Ψ₂ → ∀ φ, IsContAut (c.X j) φ → ∀ α β, c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ (w.ε j α).support, w.ε j α g • t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (w.eQT j h) Ψ₂)) = (w.cQ j * w.εT (j + 1 + 1) h β 1) • ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
  intro D c v t w hc ht hv hW hpin j h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α β
  obtain ⟨F, hF⟩ := id hpin
  obtain ⟨hX, hY⟩ := _root_.GlobalTheory.QPl.pins_keep_theta D c v t w F hc hF j h Ψ₁ Ψ₂ hΨ₁.1 hΨ₂.1
  have hom : ∀ g, IsThetaFunO c.ψ _ _ (t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁)) := by
    intro g
    rw [← (ht.sBF j 0 h).1]
    exact (t.sBF j 0 h).weil.om_pres _ _ hX
  have lin := fun (s : Finset (GA D (c.V j))) (a : GA D (c.V j) → ℂ) => (GlobalTheory.T.lastDoubleThetaLift_integrable_linear D c v t hc ht hW j h _ hY φ hφ).2 _ s a _ hom
  have hcore := GlobalTheory.T.seeSaw_last_two_steps_all_twist_places D c v t w F hc ht hv hW hF j h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α β
  have hs : ∀ i, (F.Q i).s = j := fun i => by have := (F.Q i).hs; omega
  have hidx : ∀ i, ((F.Q i).idx (j + 1) : ℂ) ≠ 0 ∧ ((F.Q i).idx (j + 1 + 1) : ℂ) ≠ 0 := by
    intro i
    have h1 := _root_.GlobalTheory.QPl.QAt.idx_last_ne_zero D c v F.χ (F.Q i)
    rw [hs i] at h1
    exact ⟨Nat.cast_ne_zero.2 h1.1, Nat.cast_ne_zero.2 h1.2⟩
  have htop : ∀ i u, (F.Q i).wt (j + 1 + 1) u = (F.Q i).idx (j + 1 + 1) := by
    intro i
    have h1 := (F.Q i).wt_top
    rw [hs i] at h1
    exact h1
  set E := conv (List.ofFn fun i => (F.Q i).εL j (F.eqv j α i)) with hE
  set P := ∏ i, (F.Q i).wt j (F.eqv j α i) with hP
  set Z := fun g => t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁) with hZ
  have hε : w.ε j α = P • E := hF.ε j 0 h α
  have hsum : ∑ g ∈ (w.ε j α).support, w.ε j α g • Z g = ∑ g ∈ E.support, (P * E g) • Z g := by
    rw [hε]
    by_cases hP0 : P = 0
    · simp [hP0]
    · rw [Finsupp.support_smul_eq hP0]
      rfl
  have hL : c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h)
      (∑ g ∈ (w.ε j α).support, w.ε j α g • Z g) (comb c.ψ _ _ (w.eQT j h) Ψ₂)) =
      P • c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h)
        (∑ g ∈ E.support, E g • Z g) (comb c.ψ _ _ (w.eQT j h) Ψ₂)) := by
    rw [hsum, ← lin E.support (fun g => P * E g), ← lin E.support (fun g => E g), Finset.smul_sum]
    exact Finset.sum_congr rfl fun g _ => by rw [smul_smul]
  simp only [hZ] at hL
  rw [hL]
  have hR : ∀ γ, c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β)
      (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) = (P * ∏ i, (F.Q i).wt (j + 1) (F.eqv (j + 1) γ i)) •
      c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ (aconv (List.ofFn fun i => (F.Q i).dL j (F.eqv j α i) (F.eqv (j + 1) γ i)))
        (aconv (List.ofFn fun i => (F.Q i).dL (j + 1) (F.eqv (j + 1) γ i) (F.eqv (j + 1 + 1) β i)))
        (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
    intro γ
    rw [hF.dQ j (by omega) α γ, hF.dQ (j + 1) (by omega) γ β, biComb_smul, block_smul₂]
  simp only [hR]
  have hεT : w.εT (j + 1 + 1) h β 1 = ∏ i, ((F.Q i).idx (j + 1 + 1) : ℂ) := by
    rw [hF.εT (j + 1 + 1) h β, Finsupp.single_eq_same]
    exact Finset.prod_congr rfl fun i _ => htop i _
  rw [hεT, hF.cQ j (by omega)]
  simp only [← smul_smul]
  rw [← Finset.smul_sum, ← hcore, smul_smul, smul_smul, smul_smul]
  congr 1
  have hone : (∏ i, (((F.Q i).idx (j + 1) : ℂ) * ((F.Q i).idx (j + 1 + 1) : ℂ))⁻¹) *
      (∏ i, ((F.Q i).idx (j + 1 + 1) : ℂ)) * ∏ i, ((F.Q i).idx (j + 1) : ℂ) = 1 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    field_simp [(hidx i).1, (hidx i).2]
  linear_combination (-P) * hone

theorem qLast_of_pin : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is →
    WeilOK (t := t) v → QPin v w → QLast v w := by
  intro D c v t w hc ht hv hW hpin j h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ f hf _
  obtain ⟨F, hF⟩ := id hpin
  obtain ⟨hX, hY⟩ := _root_.GlobalTheory.QPl.pins_keep_theta D c v t w F hc hF j h Ψ₁ Ψ₂ hΨ₁.1 hΨ₂.1
  have hfc : IsContAut c.T f := ⟨fun γ hγ g => hf.left γ hγ g, hf.cont⟩
  have hom : ∀ g, IsThetaFunO c.ψ _ _ (t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁)) := by
    intro g
    rw [← (ht.sBF j 0 h).1]
    exact (t.sBF j 0 h).weil.om_pres _ _ hX
  have han := fun α => GlobalTheory.T.lastDoubleThetaLift_integrable_linear D c v t hc ht hW j h _ hY (φ α) (hφ α).1
  set Y := comb c.ψ _ _ (w.eQT j h) Ψ₂ with hYd
  set X := comb c.ψ _ _ (w.eQ j) Ψ₁ with hXd
  set E := (c.oT (j + 1 + 1) h).emb with hE
  set K := fun α γ β => c.bl j (t.kom j) (t.kom (j + 1)) (φ α)
    (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) with hK
  set G := fun α => c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (c.lst j h (v.τ j h) (t.sBF j 0 h)
    (∑ g ∈ (w.ε j α).support, w.ε j α g • t.om j (g, 1) X) Y) with hG
  have key : ∀ α, (fun h' => f h' * G α (E (h', 1))) = fun h' => ∑ g ∈ (w.ε j α).support, w.ε j α g *
      (f h' * c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (c.lst j h (v.τ j h) (t.sBF j 0 h) (t.om j (g, 1) X) Y) (E (h', 1))) := by
    intro α
    funext h'
    simp only [hG]
    rw [← (han α).2 _ _ _ _ hom, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hint : ∀ α, IntegrableOn (fun h' => f h' * G α (E (h', 1))) c.volT.𝓕 c.volT.μ := by
    intro α
    rw [key α]
    exact integrable_finsetSum _ fun g _ => ((han α).1 _ (hom g) f hfc).const_mul _
  have hL : ∀ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) (φ α)
      (c.lst j h (v.τ j h) (t.sBF j 0 h) (t.om j (g, 1) X) Y) (E (h', 1)) ∂c.volT.μ =
      ∫ h' in c.volT.𝓕, f h' * G α (E (h', 1)) ∂c.volT.μ := by
    intro α
    rw [key α, integral_finsetSum _ fun g _ => ((han α).1 _ (hom g) f hfc).const_mul _]
    exact Finset.sum_congr rfl fun g _ => (integral_const_mul _ _).symm
  rw [Finset.sum_congr rfl fun α _ => hL α, ← integral_finsetSum _ fun α _ => hint α]

  have hcard : Fintype.card (t.Ch (j + 1 + 1)) = 1 := by
    rw [Fintype.card_congr (F.eqv (j + 1 + 1)), Fintype.card_pi]
    refine Finset.prod_eq_one fun i _ => ?_
    have hs : (F.Q i).s = j := by have := (F.Q i).hs; omega
    have h1 := (F.Q i).one
    rw [hs] at h1
    exact h1
  have hβ : ∀ β, (w.cQ j * ∫ h' in c.volT.𝓕, trc (w.εT (j + 1 + 1) h β) f h' *
      (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β)
        (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂))) (E (h', 1)) ∂c.volT.μ) =
      ∫ h' in c.volT.𝓕, ∑ α, f h' * G α (E (h', 1)) ∂c.volT.μ := by
    intro β
    have htrc : trc (w.εT (j + 1 + 1) h β) f = w.εT (j + 1 + 1) h β 1 • f := by
      rw [hF.εT (j + 1 + 1) h β]
      by_cases ha : (∏ i, (F.Q i).wt (j + 1 + 1) (F.eqv (j + 1 + 1) β i)) = 0
      · simp [trc, ha]
      · rw [trc, Finsupp.support_single _ ha, Finset.sum_singleton]
        funext x
        simp [rTrans]
    rw [← integral_const_mul]
    congr 1
    funext h'
    have hG' : ∀ α, G α = (w.cQ j * w.εT (j + 1 + 1) h β 1) • ∑ γ, K α γ β := fun α =>
      alg_of_core D c v t w hc ht hv hW hpin j h Ψ₁ Ψ₂ hΨ₁ hΨ₂ (φ α) (hφ α).1 α β
    simp only [hG', htrc, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ => ?_
    ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun β _ => hβ β, Finset.sum_const, Finset.card_univ, hcard, one_smul]

end GlobalTheory.QLastPf
end

