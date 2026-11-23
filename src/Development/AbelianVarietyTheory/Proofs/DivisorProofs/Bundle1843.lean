module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1839
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsSupLatticeSplitOverComponents
section
noncomputable section

namespace GlobalTheory.CuspSplit

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 200000

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem idem_mul_mem_cuspOn (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c) {G : WTZ D.host.E}
    (F : cuspW Xo c U G) : idem Z * (F : Rul Xo c) ∈ cuspOn U Z G := by
  refine ⟨GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2, ?_⟩
  rw [mul_comm]
  exact mul_mem_suppOn _ (idem_mem_suppOn Z)

theorem idem_mul_of_mem_cuspOn {Z : Comp Xo c} {G : WTZ D.host.E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) :
    idem Z * f = f :=
  (mem_suppOn_iff_idem_mul (cuspW_le_secZ G hf.1) Z).1 hf.2

theorem idem_mul_eq_zero {Z Z' : Comp Xo c} (h : Z ≠ Z') {G : WTZ D.host.E} {f : Rul Xo c}
    (hf : f ∈ cuspOn U Z' G) : idem Z * f = 0 := by
  calc idem Z * f = idem Z * (idem Z' * f) := by rw [idem_mul_of_mem_cuspOn hf]
    _ = 0 := by rw [← mul_assoc, idem_mul_idem_of_ne h, zero_mul]

theorem finsum_parts (f : Rul Xo c) : ∑ᶠ Z : Comp Xo c, idem Z * f = f := by
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  rw [finsum_eq_sum_of_fintype, sum_idem_mul]

theorem mem_latOn_part (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G : WTZ D.host.E} (F : cuspW Xo c U G)
    (hF : F ∈ latW U G) (Z : Comp Xo c) :
    (⟨_, idem_mul_mem_cuspOn hU Z F⟩ : cuspOn U Z G) ∈ latOn U Z G := by
  rw [latOn, mem_supLat_iff (idem_mul_mem_cuspOn hU Z F).2]
  intro la v hv
  show 0 ≤ v (idem Z * (F : Rul Xo c))
  rw [(isVal_valOn hv).mul, val_idem hv, zero_add]
  exact (mem_supLat.1 hF) la v (valOn_subset Z la hv)

theorem mem_latW_of_parts (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G : WTZ D.host.E} (F : cuspW Xo c U G)
    (h : ∀ Z, (⟨_, idem_mul_mem_cuspOn hU Z F⟩ : cuspOn U Z G) ∈ latOn U Z G) : F ∈ latW U G := by
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  refine mem_supLat.2 ?_
  intro la v hv
  have hval := isVal_valSet la v hv
  rw [← sum_idem_mul (F : Rul Xo c)]
  refine Finset.sum_induction _ (fun x => 0 ≤ v x) (fun a b ha hb => (le_min ha hb).trans (hval.add a b))
    (by rw [hval.zero]; exact le_top) fun Z _ => ?_
  exact (mem_supLat.1 ((mem_latOn U).1 (h Z))) la v hv

theorem cuspOn_indep (G : WTZ D.host.E) : iSupIndep (fun Z : Comp Xo c => cuspOn U Z G) := fun Z => by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ Z), cuspOn U j G) ≤ LinearMap.ker (LinearMap.mulLeft c.F (idem Z)) :=
    iSup₂_le fun j hj y hy => by
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply]
      exact idem_mul_eq_zero (Ne.symm hj) hy
  have h0 : idem Z * x = 0 := by
    have := hle hx'
    rwa [LinearMap.mem_ker, LinearMap.mulLeft_apply] at this
  calc x = idem Z * x := (idem_mul_of_mem_cuspOn hx).symm
    _ = 0 := h0

theorem iSup_cuspOn (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (G : WTZ D.host.E) :
    ⨆ Z : Comp Xo c, cuspOn U Z G = cuspW Xo c U G := by
  refine le_antisymm (iSup_le fun Z => cuspOn_le U Z G) fun F hF => ?_
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  rw [← sum_idem_mul F]
  exact Submodule.sum_mem _ fun Z _ => Submodule.mem_iSup_of_mem Z (idem_mul_mem_cuspOn hU Z ⟨F, hF⟩)

theorem coe_mem_of_mem_partLat {Z : Comp Xo c} {G : WTZ D.host.E} {g : cuspW Xo c U G}
    (hg : g ∈ partLat U Z G) : (g : Rul Xo c) ∈ cuspOn U Z G := by
  obtain ⟨f, -, rfl⟩ := hg
  exact f.2

theorem partLat_indep (G : WTZ D.host.E) : iSupIndep (fun Z : Comp Xo c => partLat U Z G) := fun Z => by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ Z), partLat U j G) ≤
      (LinearMap.ker ((LinearMap.mulLeft c.F (idem Z)).comp (cuspW Xo c U G).subtype)).restrictScalars (𝓞 c.F) :=
    iSup₂_le fun j hj y hy => by
      rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.mulLeft_apply]
      exact idem_mul_eq_zero (Ne.symm hj) (coe_mem_of_mem_partLat hy)
  have h0 : idem Z * (x : Rul Xo c) = 0 := by
    have := hle hx'
    rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.mulLeft_apply] at this
  apply Subtype.ext
  calc (x : Rul Xo c) = idem Z * x := (idem_mul_of_mem_cuspOn (coe_mem_of_mem_partLat hx)).symm
    _ = 0 := h0

theorem iSup_partLat (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (G : WTZ D.host.E) :
    ⨆ Z : Comp Xo c, partLat U Z G = latW U G := by
  refine le_antisymm (iSup_le fun Z => partLat_le U Z G) fun F hF => ?_
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  have hF' : F = ∑ Z : Comp Xo c,
      (⟨idem Z * (F : Rul Xo c), GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2⟩ : cuspW Xo c U G) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact (sum_idem_mul _).symm
  rw [hF']
  refine Submodule.sum_mem _ fun Z _ => Submodule.mem_iSup_of_mem Z ?_
  exact ⟨⟨_, idem_mul_mem_cuspOn hU Z F⟩, mem_latOn_part hU F hF Z, rfl⟩

theorem splits : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ G : WTZ D.host.E, Splits U G :=
  fun _ _ _ _ _ _ _ _ _ _ hU G =>
    ⟨fun F => ⟨(finsum_parts _).symm, fun Z => idem_mul_mem_cuspOn hU Z F,
        ⟨fun hF Z => mem_latOn_part hU F hF Z, mem_latW_of_parts hU F⟩⟩,
      ⟨cuspOn_indep G, iSup_cuspOn hU G⟩, partLat_indep G, iSup_partLat hU G⟩

end GlobalTheory.CuspSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseOpenEqTopOfSmoothOfRelativeDimensionZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory

theorem dense_open_eq_top_of_smoothOfRelativeDimension_zero : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k), SmoothOfRelativeDimension 0 p → ∀ (U : Y.Opens), Dense (U : Set Y) → U = ⊤ := by
  intro k _ Y p hp U hU
  have he : Etale p := (Etale.iff_smoothOfRelativeDimension_zero p).2 hp
  have hq : LocallyQuasiFinite p := by
    refine ⟨fun {V} hV {W} hW e ↦ ?_⟩
    have h := p.etale_appLE hV hW e
    letI := (p.appLE V W e).hom.toAlgebra
    have : Algebra.Etale Γ(Sp k, V) Γ(Y, W) := h
    exact (inferInstance : Algebra.QuasiFinite Γ(Sp k, V) Γ(Y, W))
  have hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hopen : ∀ y : Y, IsOpen ({y} : Set Y) := by
    intro y
    have hd : _root_.IsDiscrete (p ⁻¹' {p y}) := p.isDiscrete_preimage_singleton (p y)
    have huniv : p ⁻¹' {p y} = Set.univ := by
      ext z; simp [Subsingleton.elim (p z) (p y)]
    rw [huniv] at hd
    have : DiscreteTopology Y := by
      have h2 := hd.to_subtype
      exact (Homeomorph.Set.univ Y).symm.isEmbedding.discreteTopology
    exact isOpen_discrete _
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨z, hz1, hz2⟩ := hU.inter_open_nonempty {y} (hopen y) ⟨y, rfl⟩
  rw [Set.mem_singleton_iff] at hz1
  subst hz1
  exact hz2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivLeSubMulDiv
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

section GapArith

variable {N : ℕ}

theorem gap_add (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]
    ring
  · simp

theorem gap_sub (v w : Fin N → ℤ) (k : ℕ) : gap (v - w) k = gap v k - gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.sub_apply]
    ring
  · simp

theorem gap_nsmul (n : ℕ) (v : Fin N → ℤ) (k : ℕ) : gap (n • v) k = n * gap v k := by
  unfold gap
  split_ifs
  · simp only [Pi.smul_apply, nsmul_eq_mul]
    ring
  · simp

end GapArith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem gap_kap (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) : gap (FlagTan.kap Dw τ) k =
    if k + 1 = Dw.p then 2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2 else -2 := by
  unfold FlagTan.kap gap
  simp only [dif_pos h]
  split_ifs <;> push_cast <;> omega

theorem gap_kap_le (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) :
    gap (FlagTan.kap Dw τ) k ≤ 2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2 := by
  rw [gap_kap τ h]
  split_ifs <;> omega

theorem div_le_sub_mul_div (g : ℤ) {n : ℤ} (hn : 0 < n) : g / n ≤ g - (n - 1) * (g / n) := by
  have h₁ : n * (g / n) ≤ g := by
    first
      | exact Int.mul_ediv_self_le hn.ne'
      | exact Int.mul_ediv_le hn g
      | (have := Int.emod_def g n; have := Int.emod_nonneg g hn.ne'; linarith)
      | (have := Int.ediv_mul_le g hn.ne'; linarith)
      | (have := Int.emod_add_mul_ediv g n; have := Int.emod_nonneg g hn.ne'; linarith)
  linarith

theorem gaps_of_wtBig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (P : WtPar Dw), WtBig P → ∀ la ∈ [P.u₁, P.u₂, P.ub, P.u₁ - FlagTan.kap Dw - (dimFlag Dw + 2) • P.ub], GapGe 1 la ∧ GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) := by
  intro E _ _ _ H Dw P hP la hla
  have hD3 : (0 : ℤ) < (dimFlag Dw : ℤ) + 3 := by positivity
  have hmain : ∀ (τ : Psi H) (k : ℕ), k + 1 < Dw.p + Dw.q →
      (((dimFlag Dw + 1).choose 2 : ℕ) : ℤ) + 4 * ((Dw.p : ℤ) + Dw.q) + dimFlag Dw + 3 ≤ gap (P.ub τ) k ∧
      gap (P.ub τ) k ≤ gap (P.u₁ τ) k - ((dimFlag Dw : ℤ) + 2) * gap (P.ub τ) k ∧
      gap (P.u₁ τ) k ≤ gap (P.u₂ τ) k := by
    intro τ k h
    have hg := hP.gaps τ k h
    push_cast at hg
    rw [P.gap_ub τ h]
    refine ⟨?_, ?_, ?_⟩
    · apply Int.le_ediv_of_mul_le hD3
      linarith
    · have := div_le_sub_mul_div (gap (P.u₁ τ) k) hD3
      linarith
    · rw [show P.u₂ τ = P.u₁ τ + P.rem τ from rfl, gap_add]
      linarith [(P.gap_rem τ k).1]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hla
  rcases hla with rfl | rfl | rfl | rfl <;> constructor <;> intro τ k h <;>
  · obtain ⟨h₁, h₂, h₃⟩ := hmain τ k h
    have h₄ := gap_kap_le τ h
    push_cast at h₄
    have hC : (0 : ℤ) ≤ (((dimFlag Dw + 1).choose 2 : ℕ) : ℤ) := by positivity
    have hD : (0 : ℤ) ≤ (dimFlag Dw : ℤ) := by positivity
    have hN : (2 : ℤ) ≤ (Dw.p : ℤ) + Dw.q := by omega
    have hb : (0 : ℤ) ≤ ((dimFlag Dw : ℤ) + 2) * gap (P.ub τ) k := by
      apply mul_nonneg <;> linarith
    try simp only [Pi.sub_apply, Pi.smul_apply, gap_sub, gap_nsmul]
    try push_cast
    linarith

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumConditionStableLatticeStabilizerIne
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacTransport

theorem acts_dblVacCond_of_mem_KAtD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v),
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ))) → Acts (evFin F v) (omd g) φ φ₁ →
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ₁)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ₁))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v dd omd hsp θ hθ g hg φ hφ φ₁ hφ₁ hvac hAct w₁ hw₁ w₂ hw₂ r hr
  have hS := hsp.2.1
  have etens : ∀ (c : ℂ) (f : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) r = c • tens (evFin F v) f r := fun c f => by
    funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
  by_cases h0 : φ₁ = 0
  · subst h0
    have e0 : tens (evFin F v) (0 : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext x; simp [tens]
    rw [smul_zero, e0]
    funext x
    simp [Darboux.rho, schr]
  have hrφ : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  obtain ⟨δ₁, k₁, δ₂, k₂, he⟩ := GlobalTheory.DblVacLine.fromCols_mul_transpose G.V' G.W v (GlobalTheory.InertDbl.matD g⁻¹)
    (fun z hz => (hg.2 z hz).2) hw₁ hw₂
  have hback : actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) g (Matrix.fromCols δ₁ δ₂) = Matrix.fromCols w₁ w₂ := by
    change Matrix.fromCols δ₁ δ₂ * (GlobalTheory.InertDbl.matD g)ᵀ = _
    have e : GlobalTheory.InertDbl.matD g * GlobalTheory.InertDbl.matD g⁻¹ = 1 := Units.mul_inv g.1
    rw [← he, Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
  have hsym : symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
        (Matrix.fromCols δ₁ δ₂) (Matrix.fromCols δ₁ δ₂) =
      symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
        (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂) := by
    rw [← he]
    exact GlobalTheory.InertSph.symp_mul_transpose (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) _ _ _ (GlobalTheory.InertDbl.matD g⁻¹) (g⁻¹).2 _
  have hi := hS.impl g (Matrix.fromCols δ₁ δ₂) _ hrφ.2
  simp only [actB] at hback hi
  rw [hback] at hi
  rw [← hAct r hrφ, ← hi, hvac δ₁ k₁ δ₂ k₂ r hrφ, hsym, etens, map_smul, hAct r hrφ, etens]

end GlobalTheory.DblVacTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunctionStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeil_inert_place_vacuum_eigenfunction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
      IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @GlobalTheory.DblVacLine.dblFun_eigen | exact GlobalTheory.DblVacLine.dblFun_eigen | (intros; apply GlobalTheory.DblVacLine.dblFun_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfHeadWt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefStep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}


open Classical in
def stepEx (σ : E →+* ℂ) (j : ℕ) : Ix Dw → ℤ :=
  fun ix => ix.elim 0 fun p => if p.1 = σ ∧ (p.2 : ℕ) < j then 1 else 0


open Classical in
theorem exOf_tailWt (τ : Psi H) (k : ℕ) (hk : Dw.p ≤ k) :
    AllWt.exOf Dw (GlobalTheory.NefWt.tailWt τ k) 0 = stepEx (conjEmb τ.1) (Dw.p + Dw.q - 1 - k) := by
  refine FlagMod.exOf_ext rfl (fun τ' i hi => ?_) (fun τ' i hi => ?_)
  · have h1 : ¬ (τ' = τ ∧ k < (i : ℕ)) := fun h => by
      have := i.2; have := FlagMod.mult_of_mem (Dw := Dw) τ'; omega
    have h2 : ¬ (τ'.1 = conjEmb τ.1 ∧ (i : ℕ) < Dw.p + Dw.q - 1 - k) := fun h =>
      GlobalTheory.AllWt.conj_not_mem τ (h.1 ▸ τ'.2)
    simp only [GlobalTheory.NefWt.tailWt, stepEx, Option.elim, if_neg h1, if_neg h2]
  · have hq := FlagMod.mult_conj (Dw := Dw) τ'
    have hi' := i.2
    by_cases e : τ' = τ
    · subst e
      have : k < Dw.p + (Dw.q - 1 - (i : ℕ)) ↔ (i : ℕ) < Dw.p + Dw.q - 1 - k := by omega
      by_cases h : (i : ℕ) < Dw.p + Dw.q - 1 - k
      · simp [GlobalTheory.NefWt.tailWt, stepEx, h, this.2 h]
      · simp [GlobalTheory.NefWt.tailWt, stepEx, h, mt this.1 h]
    · have hc : conjEmb τ'.1 ≠ conjEmb τ.1 := fun h => e (Subtype.ext (by
        rw [← GlobalTheory.AllWt.conjEmb_conjEmb τ'.1, h, GlobalTheory.AllWt.conjEmb_conjEmb]))
      simp [GlobalTheory.NefWt.tailWt, stepEx, e, hc]


open Classical in
theorem exOf_headWt (τ : Psi H) (k : ℕ) (hk : k < Dw.p) :
    AllWt.exOf Dw (GlobalTheory.NefWt.headWt τ k) 0 = stepEx τ.1 (k + 1) := by
  refine FlagMod.exOf_ext rfl (fun τ' i hi => ?_) (fun τ' i hi => ?_)
  · by_cases e : τ' = τ
    · subst e
      by_cases h : (i : ℕ) ≤ k
      · simp [GlobalTheory.NefWt.headWt, stepEx, h, Nat.lt_succ_of_le h]
      · simp [GlobalTheory.NefWt.headWt, stepEx, h, show ¬ (i : ℕ) < k + 1 by omega]
    · have hc : τ'.1 ≠ τ.1 := fun h => e (Subtype.ext h)
      simp [GlobalTheory.NefWt.headWt, stepEx, e, hc]
  · have hq := FlagMod.mult_conj (Dw := Dw) τ'
    have h1 : ¬ (τ' = τ ∧ Dw.p + (Dw.q - 1 - (i : ℕ)) ≤ k) := fun h => by omega
    have h2 : ¬ (conjEmb τ'.1 = τ.1 ∧ (i : ℕ) < k + 1) := fun h =>
      GlobalTheory.AllWt.conj_not_mem τ' (h.1 ▸ τ.2)
    simp only [GlobalTheory.NefWt.headWt, stepEx, Option.elim, if_neg h1, if_neg h2, neg_zero]

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagMod.FlagCover Y)
  (Z : Comp Xo c)

theorem L₀_tailWt (τ : Psi H) (k : ℕ) (hk : Dw.p ≤ k) :
    L₀ X Z (GlobalTheory.NefWt.tailWt τ k) = LL₀ X Z (stepEx (conjEmb τ.1) (Dw.p + Dw.q - 1 - k)) :=
  congrArg (LL₀ X Z) (exOf_tailWt τ k hk)

theorem L₀_headWt (τ : Psi H) (k : ℕ) (hk : k < Dw.p) :
    L₀ X Z (GlobalTheory.NefWt.headWt τ k) = LL₀ X Z (stepEx τ.1 (k + 1)) :=
  congrArg (LL₀ X Z) (exOf_headWt τ k hk)

end GlobalTheory.NefStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorDefiniteUnitaryConjugateStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bounded_denominator_definiteUnitary_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ x : finU (E := E) (n := n), ∃ d : ℕ, 0 < d ∧ ∀ g : finU (E := E) (n := n), (∀ w ∈ S, cLoc w ((x⁻¹ * g * x : finU (E := E) (n := n)) : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n)) → ∀ (w : Pl E) (i j : Fin n), (d : w.adicCompletion E) * (cLoc w (g : UA E n)).val i j ∈ w.adicCompletionIntegers E := by
  first | exact @GlobalTheory.BCT.StabDenom.exists_denom | exact GlobalTheory.BCT.StabDenom.exists_denom | (intros; apply GlobalTheory.BCT.StabDenom.exists_denom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_action_exists : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.ActsEx := by
  first | exact @GlobalTheory.ThK.LocalOps.actsEx | exact GlobalTheory.ThK.LocalOps.actsEx | (intros; apply GlobalTheory.ThK.LocalOps.actsEx <;> assumption)
end

