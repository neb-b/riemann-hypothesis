module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0979
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthUniqueMaximalOfCyclic
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem howe_finiteLength_uniqueMaximal_of_cyclic : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) → (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) → ∀ (C : Submodule ℂ V) (α β α' β' : T → ℂ), (∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) C ⊤) → (∀ B : ℚ, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ ∀ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ B) → (⨅ w, hwSub (a w) (μ w)) ≤ U ⊔ C) → (∃ (μ : ∀ w, Ix (R w) (S w) → ℚ) (v : V), (∀ w, v ∈ hwSub (a w) (μ w)) ∧ (∀ N : Submodule ℂ V, (∀ w, Stab (a w) N) → C ≤ N → v ∈ N → N = ⊤) ∧ (⨅ w, hwSub (a w) (μ w)) ≤ Submodule.span ℂ {v} ⊔ C) → HoweAlg a C := by
  intro T _ _ R S V _ _ a hG hc C α β α' β' hQ hAdm hCyc
  refine ⟨?_, ?_⟩
  · obtain ⟨B, hB⟩ := Places.multi_place_step T R S α β α' β'
    obtain ⟨U, hU, hUC⟩ := hAdm B
    let G : Submodule ℂ V := ⨆ (μ : ∀ w, Ix (R w) (S w) → ℚ) (_ : ∀ w c, |μ w c| ≤ B), ⨅ w, hwSub (a w) (μ w)
    have hGUC : G ≤ U ⊔ C := iSup_le fun μ => iSup_le fun h => hUC μ h
    refine ⟨Module.finrank ℂ U + 1, fun m N hN hNk => ?_⟩
    refine chain_length_le_finrank_add_one V G U C hU hGUC m N hN (fun k => (hNk k).2) ?_
    intro k l hkl
    have hQ' : ∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) (N k) (N l) := fun w c d u _ =>
      ⟨(hNk k).2 (hQ w c d u Submodule.mem_top).1, (hNk k).2 (hQ w c d u Submodule.mem_top).2⟩
    obtain ⟨μ, hμB, v, hvl, hvhw, hvk⟩ :=
      hB V a hG hc (N k) (N l) (hN hkl) (fun w => (hNk k).1 w) (fun w => (hNk l).1 w) hQ'
    refine ⟨v, hvl, ?_, hvk⟩
    have hv : v ∈ ⨅ w, hwSub (a w) (μ w) := Submodule.mem_iInf _ |>.mpr hvhw
    exact (le_iSup_of_le μ (le_iSup_of_le hμB le_rfl) : (⨅ w, hwSub (a w) (μ w)) ≤ G) hv
  · intro N N' hN hCN hNt hN' hCN' hN't hsup
    obtain ⟨μ, v, hvhw, hgen, hmult⟩ := hCyc
    have hv : v ∈ ⨅ w, hwSub (a w) (μ w) := Submodule.mem_iInf _ |>.mpr hvhw
    have hv2 : v ∈ (N ⊔ N') ⊓ ⨅ w, hwSub (a w) (μ w) := ⟨by rw [hsup]; exact Submodule.mem_top, hv⟩
    have hsp := hw_joint_split T R S V a hG hc N N' hN hN' μ hv2
    obtain ⟨n, hn, n', hn', hnn⟩ := Submodule.mem_sup.mp hsp
    obtain ⟨y, hy, c, hc', hyc⟩ := Submodule.mem_sup.mp (hmult hn.2)
    obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hy
    by_cases hx : x = 0
    · subst hx
      have hnC : n = c := by rw [← hyc]; simp
      have hvN' : v ∈ N' := by
        rw [← hnn]; exact N'.add_mem (hCN' (hnC ▸ hc')) hn'.1
      exact hN't (hgen N' hN' hCN' hvN')
    · have hvN : v ∈ N := by
        have h1 : x • v ∈ N := by
          have : x • v = n - c := by rw [← hyc]; simp
          rw [this]; exact N.sub_mem hn.1 (hCN hc')
        have := N.smul_mem x⁻¹ h1
        rwa [smul_smul, inv_mul_cancel₀ hx, one_smul] at this
      exact hNt (hgen N hN hCN hvN)

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledEigenfunctionsLineVacuum
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.VDblLine

theorem vdbl_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • G.M.vac v)) →
    ∀ φ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ)) → ∃ c : ℂ, φ = c • (boxFun (G.M.vac v) (fun x => star (G.M.vac v x))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv d' hd' dd hdc θ hθ hvac φ hφSB hφ
  classical
  have hψ := hT.base.std
  have hn := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  have hnv : ∀ t, ‖GlobalTheory.LatVac.psiAt B.ψ v t‖ = 1 := fun t => hn (GlobalTheory.LatVac.liftV v t)
  set Λ := latAtV G.V G.W v with hΛ
  have hat : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  have hatT : ∀ γ ∈ Λ, At (evFin F v) γᵀ := fun γ h u hu => by
    rw [← Matrix.transpose_smul, hat γ h u hu, Matrix.transpose_zero]
  obtain ⟨hvSB, hv0, -⟩ := hT.geo.hM.vac v
  set φ₀ := G.M.vac v with hφ₀
  set φd := boxFun φ₀ (fun x => star (φ₀ x)) with hφd

  have loc : ∀ {κ : Type} [Fintype κ] {W' : Type} [AddCommGroup W'] [Module (AF F) W'] {Bf : W' → W' → AF F}
      (d : Darboux Bf κ) (f : (κ → Fv F v) → ℂ), f ∈ SB _ → ∀ γ, At (evFin F v) γ → ∀ c : ℂ,
      Acts (evFin F v) (d.rho B.ψ γ) f (c • f) →
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo d v γ) f = c • f := by
    intro κ _ W' _ _ Bf d f hf γ hγ c h
    obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v f hf
    refine GlobalTheory.DblVacLine.eq_of_tens v hr.1 hx₀ ?_
    rw [← GlobalTheory.VacBridge.rho_acts_locCo d B.ψ v γ hγ f r hr]
    exact h r hr
  have hco : ∀ w₁ w₂ : Matrix (Fin a) (Fin (a + a')) (AE F E),
      GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ᵀ w₂ᵀ) =
      (Sum.elim (GlobalTheory.LatVac.locCo G.M.co v w₁).1 (GlobalTheory.LatVac.locCo G.M.co v w₂).1,
        Sum.elim (GlobalTheory.LatVac.locCo G.M.co v w₁).2 (-(GlobalTheory.LatVac.locCo G.M.co v w₂).2)) := by
    intro w₁ w₂
    change ((fun k => evFin F v ((dd.e (Matrix.fromCols w₁ᵀ w₂ᵀ)).1 k)),
      fun k => evFin F v ((dd.e (Matrix.fromCols w₁ᵀ w₂ᵀ)).2 k)) = _
    rw [hdc, hd', hd']
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · cases k <;> rfl
    · cases k with
      | inl k => rfl
      | inr k => exact map_neg (evFin F v) _
  let χ : Matrix (Fin a) (Fin (a + a')) (AE F E) → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ)
  let cf : Matrix (Fin a) (Fin (a + a')) (AE F E) → Matrix (Fin a) (Fin (a + a')) (AE F E) → ℂ := fun w₁ w₂ =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
      (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ))
  have ht : ∀ w : Matrix (Fin a) (Fin (a + a')) (AE F E),
      symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) wᵀ wᵀ =
        symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w w := fun w => by
    rw [GlobalTheory.WeilTr.symp_transpose (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) _ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) wᵀ wᵀ, Matrix.transpose_transpose]
  have hcf : ∀ w₁ w₂, cf w₁ w₂ = χ w₁ * star (χ w₂) := by
    intro w₁ w₂
    simp only [cf, χ]
    rw [GlobalTheory.DblVacLine.symp_dbl, GlobalTheory.DblVacLine.star_eq_neg B.ψ hn, ht, ht, ← AddChar.map_add_eq_mul, mul_sub,
      sub_eq_add_neg]
  have hvl : ∀ γ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ₀ = χ γ • φ₀ :=
    fun γ h => loc G.M.co φ₀ hvSB γ (hat γ h) _ (hvac γ h)
  have hφl : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ,
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ = cf w₁ w₂ • φ :=
    fun w₁ h₁ w₂ h₂ => loc dd φ hφSB _ (GlobalTheory.DblVacLine.at_fromCols v (hatT w₁ h₁) (hatT w₂ h₂)) _ (hφ w₁ h₁ w₂ h₂)
  have hdl : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ,
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ᵀ w₂ᵀ)) φd = cf w₁ w₂ • φd := by
    intro w₁ h₁ w₂ h₂
    rw [hco, hφd, GlobalTheory.DblVacLine.schr_box _ hnv, hvl w₁ h₁, hvl w₂ h₂, hcf]
    funext x
    simp only [boxFun, Pi.smul_apply, smul_eq_mul, star_mul']
    ring

  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V G.W v G.M.co hT.geo.hV.lat.toIsLattice hT.geo.hW.lat.toIsLattice
  have hsd := GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ G.V G.W _ _ _ _ hT.base hT.geo.hV hT.geo.hW v
  have hfill := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt B.ψ v)
    (Λ.map (GlobalTheory.LatVac.locCo G.M.co v)) c hc0 (fun x => (hT.base.inert v w hw).2.2 x)
    (GlobalTheory.LatVac.DualLoc.map_selfDual v G.M.co B.ψ Λ hat hsd)
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  have hφd0 : φd ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hv0
    refine Function.ne_iff.mpr ⟨Sum.elim t t, ?_⟩
    show φ₀ t * star (φ₀ t) ≠ 0
    exact mul_ne_zero ht (star_ne_zero.mpr ht)
  obtain ⟨c', hc'⟩ := GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v)
    (fun i : Λ × Λ => GlobalTheory.LatVac.locCo dd v (Matrix.fromCols i.1.1ᵀ i.2.1ᵀ))
    (fun i => cf i.1.1 i.2.1) (fun u hu => by
      have eu : u = Sum.elim (u ∘ Sum.inl) (u ∘ Sum.inr) := (Sum.elim_comp_inl_inr u).symm
      obtain ⟨y₁, γ₁, h₁, e₁⟩ := hfill (u ∘ Sum.inl) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (⟨γ, hγ⟩, 0) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero]
          funext k; cases k <;> rfl)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      obtain ⟨y₂, γ₂, h₂, e₂⟩ := hfill (u ∘ Sum.inr) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (0, ⟨-γ, neg_mem hγ⟩) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg]
          funext k; cases k <;> simp)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      refine ⟨(⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩), ?_⟩
      simp only [hco, e₁, e₂]
      exact eu.symm) φ φd
    (fun i => hφl _ i.1.2 _ i.2.2) (fun i => hdl _ i.1.2 _ i.2.2) hφd0
  exact ⟨c', hc'⟩

end GlobalTheory.VDblLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledVacuumConditionUnique
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblVacUniq

theorem dbl_vac_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))), IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • (G.M'.vac v))) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ))) → ∃ c : ℂ, φ = c • (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin dd hdd θ _ hvac φ hφ hfix
  classical
  set Λ := latAtV G.V' G.W v with hΛ
  have hat : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  have hn := GlobalTheory.StdCharFromIsStd.norm_psi hTr.base.std
  have hnl : ∀ t, ‖GlobalTheory.LatVac.psiAt B.ψ v t‖ = 1 := fun t => hn _
  set vac := G.M'.vac v with hvacdef
  have hvacSB : vac ∈ SB _ := (hTr.geo.hM'.vac v).1
  have hvac0 : vac ≠ 0 := (hTr.geo.hM'.vac v).2.1
  let cf1 : Matrix (Fin a') (Fin (a + a')) (AE F E) → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ)
  let cf : Matrix (Fin a') (Fin (a + a') ⊕ Fin (a + a')) (AE F E) → ℂ := fun m =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) m m)
  have hcf : ∀ γ₁ γ₂, cf (Matrix.fromCols γ₁ γ₂) = cf1 γ₁ * star (cf1 γ₂) := by
    intro γ₁ γ₂
    simp only [cf, cf1, GlobalTheory.DblVacLine.symp_dbl, GlobalTheory.DblVacLine.star_eq_neg B.ψ hn, mul_sub]
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]

  have hl1 : ∀ γ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) vac = cf1 γ • vac := by
    intro γ hγ
    exact GlobalTheory.TensUniq.eq_of_tens_eq v vac _ _ hvacSB fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v γ (hat γ hγ) vac r hr).symm.trans (hvac γ hγ r hr)

  have hlφ : ∀ γ₁ ∈ Λ, ∀ γ₂ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols γ₁ γ₂)) φ =
      cf (Matrix.fromCols γ₁ γ₂) • φ := by
    intro γ₁ h₁ γ₂ h₂
    exact GlobalTheory.TensUniq.eq_of_tens_eq v φ _ _ hφ fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ (GlobalTheory.DblVacLine.at_fromCols v (hat _ h₁) (hat _ h₂)) φ r hr).symm.trans
        (hfix γ₁ h₁ γ₂ h₂ r hr)
  have hco : ∀ γ₁ γ₂, GlobalTheory.LatVac.locCo dd v (Matrix.fromCols γ₁ γ₂) =
      (Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v γ₁).1 (GlobalTheory.LatVac.locCo G.M'.co v γ₂).1,
        Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v γ₁).2 (-(GlobalTheory.LatVac.locCo G.M'.co v γ₂).2)) := by
    intro γ₁ γ₂
    change ((fun k => evFin F v ((dd.e (Matrix.fromCols γ₁ γ₂)).1 k)),
      fun k => evFin F v ((dd.e (Matrix.fromCols γ₁ γ₂)).2 k)) = _
    rw [hdd]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · cases k <;> rfl
    · cases k with
      | inl k => rfl
      | inr k => exact map_neg (evFin F v) _
  set φd := boxFun vac (fun x => star (vac x)) with hφd

  have hld : ∀ γ₁ ∈ Λ, ∀ γ₂ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols γ₁ γ₂)) φd =
      cf (Matrix.fromCols γ₁ γ₂) • φd := by
    intro γ₁ h₁ γ₂ h₂
    rw [hco, hφd, GlobalTheory.DblVacLine.schr_box (GlobalTheory.LatVac.psiAt B.ψ v) hnl, hl1 γ₁ h₁, hl1 γ₂ h₂, hcf]
    funext x
    simp only [boxFun, Pi.smul_apply, smul_eq_mul, star_mul']
    ring
  have hφd0 : φd ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hvac0
    refine Function.ne_iff.mpr ⟨Sum.elim t t, ?_⟩
    show vac t * star (vac t) ≠ 0
    exact mul_ne_zero ht (star_ne_zero.mpr ht)

  have hsd := GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ G.V' G.W _ _ _ _ hTr.base hTr.geo.hV' hTr.geo.hW v
  have hunr := (hTr.base.inert v w hin).2.2
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V' G.W v G.M'.co hTr.geo.hV'.lat.toIsLattice hTr.geo.hW.lat.toIsLattice
  have hfill := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt B.ψ v)
    (Λ.map (GlobalTheory.LatVac.locCo G.M'.co v)) c hc0 (fun x => hunr x) (GlobalTheory.LatVac.DualLoc.map_selfDual v G.M'.co B.ψ Λ hat hsd)
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  obtain ⟨c', hc'⟩ := GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v)
    (fun i : Λ × Λ => GlobalTheory.LatVac.locCo dd v (Matrix.fromCols i.1.1 i.2.1))
    (fun i => cf (Matrix.fromCols i.1.1 i.2.1)) (fun u hu => by
      have eu : u = Sum.elim (u ∘ Sum.inl) (u ∘ Sum.inr) := (Sum.elim_comp_inl_inr u).symm
      obtain ⟨y₁, γ₁, h₁, e₁⟩ := hfill (u ∘ Sum.inl) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (⟨γ, hγ⟩, 0) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero]
          funext k; cases k <;> rfl)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      obtain ⟨y₂, γ₂, h₂, e₂⟩ := hfill (u ∘ Sum.inr) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (0, ⟨-γ, neg_mem hγ⟩) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg]
          funext k; cases k <;> simp)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      refine ⟨(⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩), ?_⟩
      simp only [hco, e₁, e₂]
      exact eu.symm) φ φd
    (fun i => hlφ _ i.1.2 _ i.2.2) (fun i => hld _ i.1.2 _ i.2.2) hφd0
  exact ⟨c', hc'⟩

end GlobalTheory.DblVacUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberCurveOfClassEqSmulAdd
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem interNumRed_of_cls_eq_nsmul_add : ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (L M M' : LB X) (hL : L.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (a b : ℕ) (C : Closeds X), IsCompleteCurve k C → cls L hL = a • cls M hM + b • cls M' hM' → interNumRed k C ![L] = a * interNumRed k C ![M] + b * interNumRed k C ![M'] := by
  intro k _ X q hq
  letI := algebraΓOfHom q
  intro L M M' hL hM hM' a b C hC e
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hq
  rw [hC.interNumRed_of_cls_eq_add hH hL (isLB_lbPow hM a) (isLB_lbPow hM' b)
    (by rw [cls_lbPow hM, cls_lbPow hM', e]),
    hC.interNumRed_lbPow hH hM, hC.interNumRed_lbPow hH hM']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundleOfSmulClassEqAmpleAtAddNef
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem isBig_of_smul_cls_eq_add_ampleAt : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X), IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → IsBig k N := by
  intro hnum k _ X _ q hq
  letI := algebraΓOfHom q
  intro N N₁ N₂ hN h₁ h₂ a x _ ha e hx hn₂
  have hf : ∀ r, algebraMap k Γ(X, ⊤) r = q.appTop ((Scheme.ΓSpecIso (.of k)).inv r) :=
    algebraΓOfHom_algebraMap q
  have hp : IsProjOver (strHom k (X := X)) := (strHom_eq hf) ▸ hq
  obtain ⟨m, A, s, hm, hA, hAmp, hxs⟩ := hx
  have hD := Semi.LB.isLB_div (isLB_lbPow h₁ m) hA
  have hsec : HasNonzeroSec (LB.div (lbPow N₁ m) A) := ⟨s, sec_ne_zero_of_mem hxs⟩
  have hB : IsBig k (tens (lbPow N₂ m) A) := (hn₂.pow hAmp m).isBig_tens_ample hnum hp hAmp
  have hP := isLB_lbPow hN (a * m)
  have e₂ : (a * m) • cls N hN = m • (cls N₁ h₁ + cls N₂ h₂) := by
    rw [← e, smul_smul, mul_comm a m]
  have hbig : IsBig k (lbPow N (a * m)) := hB.of_cls_eq_add hf hq hD hsec hP (by
    rw [cls_tens (isLB_lbPow h₂ m) hA, cls_div (isLB_lbPow h₁ m) hA hD, cls_lbPow hN, cls_lbPow h₂,
      cls_lbPow h₁, e₂]
    module)
  exact hbig.of_pow hN (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero ha.ne' hm.ne'))
    fun n => finite_coh_zero_twist_of_isProjOver hf hq (isLB_lbPow hN n)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfForallRealValuationLeOne
section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

open IsDedekindDomain IsLocalRing

theorem exists_realValuation_of_discreteValuationSubring {Ω : Type} [Field Ω]
    (V : ValuationSubring Ω) [IsDiscreteValuationRing V] :
    ∃ ν : Valuation Ω ℝ≥0, (∀ x : V, ν (x : Ω) ≤ 1) ∧ ∀ x ∈ maximalIdeal V, ν (x : Ω) < 1 := by
  have hne : maximalIdeal V ≠ ⊥ := IsDiscreteValuationRing.not_a_field V
  let v : HeightOneSpectrum V := ⟨maximalIdeal V, inferInstance, hne⟩
  let hmono := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num))
  refine ⟨Valuation.map { WithZeroMulInt.toNNReal (e := 2) (by norm_num) with
    monotone' := hmono.monotone } (v.valuation Ω),
    fun x => ?_, fun x hx => ?_⟩
  · have h := v.valuation_le_one (K := Ω) x
    have := hmono.monotone h
    simpa using this
  · have h := (v.valuation_lt_one_iff_mem (K := Ω) x).mpr hx
    have := hmono h
    simpa using this

theorem isIntegral_of_forall_realValuation_le_one : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω], (⊤ : IntermediateField K Ω).FG → ∀ (A : Subalgebra K Ω), A.FG → ∀ t : Ω, (∀ ν : Valuation Ω ℝ≥0, (∀ a ∈ A, ν a ≤ 1) → ν t ≤ 1) → IsIntegral A t := by
  intro K Ω _ _ _ _ hfg A hA t ht
  by_contra hn
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hn isIntegral_zero
  have : Algebra.EssFiniteType K Ω := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType A Ω := .of_comp K A Ω
  have : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType A).mp hA
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have hic : IsIntegrallyClosedIn (integralClosure A Ω).toSubring Ω :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure A Ω) Ω)
  obtain ⟨W, hW, htW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure A Ω).toSubring) (x := t) hn
  have hinv : t⁻¹ ∈ W.nonunits := W.inv_mem_nonunits_iff.mpr (Or.inr htW)
  obtain ⟨V, h1, h2, -, h3⟩ := GlobalTheory.exists_discreteValuationSubring_of_valuationSubring (R := A) W
    (fun r => hW ((integralClosure A Ω).algebraMap_mem r))
    Set.finite_empty (Set.finite_singleton t⁻¹) (by simp) (by simpa using hinv)
    ⟨_, rfl, inv_ne_zero ht0⟩
  obtain ⟨ν, hν1, hνm⟩ := exists_realValuation_of_discreteValuationSubring V
  have hle : ν t ≤ 1 := ht ν fun a ha => hν1 ⟨a, h2 ⟨a, ha⟩⟩
  have hn3 : t⁻¹ ∈ V.nonunits := h3 _ rfl
  have htV : t⁻¹ ∈ V :=
    (V.valuation_le_one_iff _).mp (le_of_lt ((V.mem_nonunits_iff).mp hn3))
  have hm : (⟨t⁻¹, htV⟩ : V) ∈ maximalIdeal V :=
    (ValuationSubring.coe_mem_nonunits_iff (a := ⟨t⁻¹, htV⟩)).mp hn3
  have hlt : ν t⁻¹ < 1 := hνm _ hm
  have h1' : ν (t * t⁻¹) = 1 := by rw [mul_inv_cancel₀ ht0, map_one]
  rw [map_mul] at h1'
  have : ν t * ν t⁻¹ < 1 := lt_of_le_of_lt (mul_le_of_le_one_left zero_le hle) hlt
  exact absurd h1' this.ne

end GlobalTheory.DegVal
end

