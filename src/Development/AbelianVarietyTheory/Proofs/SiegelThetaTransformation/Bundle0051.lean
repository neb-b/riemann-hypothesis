module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatch
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.CongTop

variable {D : D7}

theorem fmt_eq (V : HSp D) (g : GA D V) : fmt V g = (finHom V g).1 := rfl

theorem fmt_one (V : HSp D) : fmt V 1 = 1 := by rw [fmt_eq, map_one, Units.val_one]

theorem fmt_mul (V : HSp D) (g h : GA D V) : fmt V (g * h) = fmt V g * fmt V h := by
  rw [fmt_eq, map_mul, Units.val_mul, fmt_eq, fmt_eq]

theorem isMov_iff (V : HSp D) (L : Lt D.host.E V.rank) (k : GA D V) :
    IsMov (fmt V k) L L ↔ (∀ u ∈ hatV L, fmt V k *ᵥ u ∈ hatV L) ∧ ∀ u ∈ hatV L, fmt V k⁻¹ *ᵥ u ∈ hatV L := by
  constructor
  · intro h
    refine ⟨fun u hu => (h _).2 ⟨u, hu, rfl⟩, fun u hu => ?_⟩
    obtain ⟨u₀, h0, rfl⟩ := (h u).1 hu
    rwa [Matrix.mulVec_mulVec, ← fmt_mul, inv_mul_cancel, fmt_one, Matrix.one_mulVec]
  · rintro ⟨h1, h2⟩ u
    constructor
    · intro hu
      refine ⟨_, h2 u hu, ?_⟩
      rw [Matrix.mulVec_mulVec, ← fmt_mul, mul_inv_cancel, fmt_one, Matrix.one_mulVec]
    · rintro ⟨u₀, h0, rfl⟩
      exact h1 _ h0

noncomputable def congSub (V : HSp D) (L : Lt D.host.E V.rank) (M : ℕ) : Subgroup (GA D V) where
  carrier := {k | CongK V L M k}
  one_mem' := by
    refine ⟨(isMov_iff V L 1).2 ⟨fun u hu => ?_, fun u hu => ?_⟩, fun u _ => ⟨0, zero_mem _, ?_⟩⟩
    · rwa [fmt_one, Matrix.one_mulVec]
    · rwa [inv_one, fmt_one, Matrix.one_mulVec]
    · rw [fmt_one, Matrix.one_mulVec, sub_self, nsmul_zero]
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    rw [isMov_iff] at ha hb
    refine ⟨(isMov_iff V L _).2 ⟨fun u hu => ?_, fun u hu => ?_⟩, fun u hu => ?_⟩
    · rw [fmt_mul, ← Matrix.mulVec_mulVec]
      exact ha.1 _ (hb.1 _ hu)
    · rw [_root_.mul_inv_rev, fmt_mul, ← Matrix.mulVec_mulVec]
      exact hb.2 _ (ha.2 _ hu)
    · obtain ⟨x, hx, ex⟩ := ha' _ (hb.1 _ hu)
      obtain ⟨y, hy, ey⟩ := hb' _ hu
      refine ⟨x + y, add_mem hx hy, ?_⟩
      rw [fmt_mul, ← Matrix.mulVec_mulVec, nsmul_add, ← ex, ← ey, sub_add_sub_cancel]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    rw [isMov_iff] at ha
    refine ⟨(isMov_iff V L _).2 ⟨ha.2, by rw [inv_inv]; exact ha.1⟩, fun u hu => ?_⟩
    obtain ⟨x, hx, ex⟩ := ha' _ (ha.2 _ hu)
    refine ⟨-x, neg_mem hx, ?_⟩
    rw [Matrix.mulVec_mulVec, ← fmt_mul, mul_inv_cancel, fmt_one, Matrix.one_mulVec] at ex
    rw [neg_nsmul, ← ex, neg_sub]

theorem isOpen_congSub (V : HSp D) (L : Lt D.host.E V.rank) (M : ℕ) (hfg : L.FG)
    (hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤) (hM : 0 < M) :
    IsOpen (congSub V L M : Set (GA D V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hn : {m : Matrix (Fin V.rank) (Fin V.rank) (AfE D) | ∀ z ∈ hatV L, ∃ y ∈ hatV L, m *ᵥ z - z = M • y} ∈
      nhds (1 : Matrix (Fin V.rank) (Fin V.rank) (AfE D)) :=
    GlobalTheory.LevelOpen.congr_mem_nhds D.host.F D.host.E V.rank _ hfg hsp M hM
  have hc : Continuous (fmt V) := GlobalTheory.Member.continuous_finHom_val D V
  have h1 := hc.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [fmt_one]; exact hn)
  have h2 := (hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds
    (by rw [Function.comp_apply, inv_one, fmt_one]; exact hn)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro k ⟨hk1, hk2⟩
  refine ⟨(isMov_iff V L k).2 ⟨fun y hy => ?_, fun y hy => ?_⟩, hk1⟩
  · obtain ⟨w, hw, h⟩ := hk1 y hy
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw M) hy
  · obtain ⟨w, hw, h⟩ := hk2 y hy
    rw [Function.comp_apply] at h
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw M) hy

theorem isClosed_GinfC (V : HSp D) : IsClosed (GinfC V : Set (GA D V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : T2Space (Af D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space
  have h : (GinfC V : Set (GA D V)) = {g | (finHom V g).1 = 1} := by
    ext g
    exact Units.ext_iff
  rw [h]
  exact isClosed_eq (GlobalTheory.Member.continuous_finHom_val D V) continuous_const

theorem isClosed_GfC (V : HSp D) : IsClosed (GfC V : Set (GA D V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Ainf D.host.F)
  haveI : T2Space (Ainf D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space
  have h : (GfC V : Set (GA D V)) = {g | (infHom V g).1 = 1} := by
    ext g
    exact Units.ext_iff
  rw [h]
  have hm : Continuous (fun k : GA D V => (matHom V k).1) :=
    Units.continuous_val.comp continuous_subtype_val
  exact isClosed_eq (hm.matrix_map (GlobalTheory.Member.continuous_infPart D)) continuous_const

theorem exists_compact (V : HSp D) (L : Lt D.host.E V.rank) (hfg : L.FG)
    (hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤) :
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ k : GA D V, IsMov (fmt V k) L L → (k ∈ GfC V ∨ V.gram = 1) → k ∈ C := by
  obtain ⟨θ₀, hθ₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  let θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun ρ => θ₀ (tauE D ρ)
  have hθ : IsInfFam θ := fun ρ => hθ₀ _
  have hsp' := (GlobalTheory.Member.Arch.archM_spec D V θ₀ hθ₀).1
  have hu : ∀ ρ h, (infMat D.sp.cm.sig V.gram (θ ρ) h)ᴴ * gramAt D V ρ * infMat D.sp.cm.sig V.gram (θ ρ) h =
      gramAt D V ρ := fun ρ h => (GlobalTheory.Member.Arch.unit_iff _ _ _).1 ((hsp' (tauE D ρ)).2.2.2.2 h)
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.StabCompact.exists_compact_entries D.host.F D.host.E L hfg hsp
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ 1 C hC
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.StabCompact.det_gram_ne_zero V) C' hC'
  refine ⟨K, hK, fun k h1 h2 => hKe k fun i j =>
    hCe' _ (hCe (fmt V k) ((isMov_iff V L k).1 h1).1 i j) fun ρ => ?_⟩
  have hU : infMat D.sp.cm.sig V.gram (θ ρ) k ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
    rcases h2 with h2 | h2
    · have h3 : (infHom V k).1 = 1 := congrArg Units.val (show infHom V k = 1 from h2)
      have h4 : infMat D.sp.cm.sig V.gram (θ ρ) k = ((infHom V k).1).map (θ ρ) := rfl
      rw [h4, h3, Matrix.map_one _ (map_zero _) (map_one _)]
      exact one_mem _
    · have h3 : gramAt D V ρ = 1 := by
        unfold gramAt
        rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]
      have h4 := hu ρ k
      rw [h3, Matrix.mul_one] at h4
      exact Matrix.mem_unitaryGroup_iff'.2 h4
  exact entry_norm_bound_of_unitary hU i j

theorem adelicUnitary_top_cong : ∀ (D : D7) (V : HSp D), IsTopologicalGroup (GA D V) ∧ LocallyCompactSpace (GA D V) ∧ SecondCountableTopology (GA D V) ∧ T2Space (GA D V) ∧ BorelSpace (GA D V) ∧ IsClosed (GinfC V : Set (GA D V)) ∧ ∀ (L : Lt D.host.E V.rank) (M : ℕ), (L.FG ∧ Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤) → 0 < M → ∃ K : Subgroup (GA D V), (∀ k, k ∈ K ↔ CongK V L M k) ∧ IsOpen (K : Set (GA D V)) ∧ IsCompact ((K : Set (GA D V)) ∩ GfC V) ∧ (V.gram = 1 → IsCompact (K : Set (GA D V))) := by
  intro D V
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have i0 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  refine ⟨i0, i1, i2, i3, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram, isClosed_GinfC V, ?_⟩
  rintro L M ⟨hfg, hsp⟩ hM
  have ho := isOpen_congSub V L M hfg hsp hM
  have hcl : IsClosed (congSub V L M : Set (GA D V)) := Subgroup.isClosed_of_isOpen _ ho
  obtain ⟨C, hC, hCm⟩ := exists_compact V L hfg hsp
  refine ⟨congSub V L M, fun _ => Iff.rfl, ho, ?_, fun hg => ?_⟩
  · exact hC.of_isClosed_subset (hcl.inter (isClosed_GfC V)) fun k hk => hCm k hk.1.1 (Or.inl hk.2)
  · exact hC.of_isClosed_subset hcl fun k hk => hCm k hk.1 (Or.inr hg)

end GlobalTheory.Ker.CongTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnnihilationCreationPeriodCoordinates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.HeisDeriv

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

theorem hx_add_left (z z' w : Fin g → ℂ) :
    hx X bas idx x (z + z') w = hx X bas idx x z w + hx X bas idx x z' w := by
  simp only [hx, Matrix.mulVec_add, add_dotProduct]

theorem hx_add_right (z w w' : Fin g → ℂ) :
    hx X bas idx x z (w + w') = hx X bas idx x z w + hx X bas idx x z w' := by
  simp only [hx, Matrix.mulVec_add, star_add, dotProduct_add]

theorem hx_smul_left (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x (c • z) w = c * hx X bas idx x z w := by
  simp only [hx, Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul]

theorem hx_smul_right (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x z (c • w) = conj c * hx X bas idx x z w := by
  simp only [hx, Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_eq_mul, Complex.star_def]

theorem hx_rsmul_left (t : ℝ) (z w : Fin g → ℂ) :
    hx X bas idx x (t • z) w = t * hx X bas idx x z w := by
  rw [← Complex.coe_smul, hx_smul_left]

theorem hx_rsmul_right (t : ℝ) (z w : Fin g → ℂ) :
    hx X bas idx x z (t • w) = t * hx X bas idx x z w := by
  rw [← Complex.coe_smul, hx_smul_right, Complex.conj_ofReal]

theorem hasDerivAt_translate (hs : ∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w))
    (Φ : (Fin n → Fin g → ℂ) → ℂ) (hΦ : Differentiable ℝ Φ) (ζ u : Fin n → Fin g → ℂ) :
    HasDerivAt (fun t : ℝ => cexp (π * I * ((∑ k, hx X bas idx x (ζ k) ((t • u) k)).im : ℝ)) *
      (gaussR X bas idx x (ζ + t • u) * Φ (ζ + t • u)))
      (gaussR X bas idx x ζ * (-(π * ∑ k, hx X bas idx x (u k) (ζ k)) * Φ ζ + fderiv ℝ Φ ζ u)) 0 := by
  have hab : ∑ k, hx X bas idx x (ζ k) (u k) = conj (∑ k, hx X bas idx x (u k) (ζ k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hs (u k) (ζ k)
  have hph : ∀ t : ℝ, (((∑ k, hx X bas idx x (ζ k) ((t • u) k)).im : ℝ) : ℂ) =
      (t : ℂ) * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ) := by
    intro t
    have h : ∑ k, hx X bas idx x (ζ k) ((t • u) k) = (t : ℂ) * ∑ k, hx X bas idx x (ζ k) (u k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, hx_rsmul_right]
    rw [h, Complex.im_ofReal_mul, Complex.ofReal_mul]
  have hq : ∀ t : ℝ, ∑ k, hx X bas idx x ((ζ + t • u) k) ((ζ + t • u) k) =
      ∑ k, hx X bas idx x (ζ k) (ζ k) +
        (t : ℂ) * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k)) +
        (t : ℂ) ^ 2 * ∑ k, hx X bas idx x (u k) (u k) := by
    intro t
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, hx_add_left, hx_add_right, hx_rsmul_left, hx_rsmul_right]
    ring
  have hT : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hE : HasDerivAt (fun t : ℝ => (Real.pi : ℂ) * I * ((t : ℂ) * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ)) -
        (Real.pi : ℂ) / 2 * (∑ k, hx X bas idx x (ζ k) (ζ k) +
          (t : ℂ) * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k)) +
          (t : ℂ) ^ 2 * ∑ k, hx X bas idx x (u k) (u k)))
      ((Real.pi : ℂ) * I * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ) -
        (Real.pi : ℂ) / 2 * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k))) 0 := by
    have h := ((hT.mul_const (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ)).const_mul ((Real.pi : ℂ) * I)).sub
      ((((hT.mul_const (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k))).const_add
        (∑ k, hx X bas idx x (ζ k) (ζ k))).add ((hT.pow 2).mul_const (∑ k, hx X bas idx x (u k) (u k)))).const_mul
          ((Real.pi : ℂ) / 2))
    exact h.congr_deriv (by simp)
  have hL : HasDerivAt (fun t : ℝ => ζ + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add ζ
  have hΦt : HasDerivAt (fun t : ℝ => Φ (ζ + t • u)) (fderiv ℝ Φ ζ u) 0 :=
    (hΦ ζ).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hL (by simp)
  have hF := hE.cexp.mul hΦt
  refine (hF.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  · have key : (Real.pi : ℂ) * I * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ) -
        (Real.pi : ℂ) / 2 * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k)) =
        -((Real.pi : ℂ) * ∑ k, hx X bas idx x (u k) (ζ k)) := by
      rw [hab]
      generalize ∑ k, hx X bas idx x (u k) (ζ k) = b
      have e1 : conj b = (b.re : ℂ) - (b.im : ℂ) * I := by apply Complex.ext <;> simp
      have e2 : b = (b.re : ℂ) + (b.im : ℂ) * I := (Complex.re_add_im b).symm
      rw [Complex.conj_im, e1]
      push_cast
      linear_combination ((Real.pi : ℂ) / 2) * e2
    rw [key]
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, add_zero, zero_smul, zero_sub,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    unfold GlobalTheory.Ker.gaussR
    ring
  · beta_reduce
    rw [hph t]
    unfold GlobalTheory.Ker.gaussR
    rw [hq t, ← mul_assoc, ← Complex.exp_add]
    congr 2

end Classical

variable {D : D7} {S T : HSp D}

theorem dRho_eq (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (G : WO S T → ℂ)
    (Φ : (Fin S.rank → Fin C.g → ℂ) → ℂ) (hΦ : Differentiable ℝ Φ)
    (hG : ∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * Φ (C.zOf (C.xB B) w))
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Fin S.rank → Fin C.g → ℂ)
    (hu : u = zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank))
    (w : WO S T) (hw : IsRealPt w) :
    Formalism.IndefR.Datum.dRho (heisO C.ψ S T) C.θ τ z G w =
      gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) *
        (-(π * ∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k)) * Φ (C.zOf (C.xB B) w) +
          fderiv ℝ Φ (C.zOf (C.xB B) w) u) := by
  obtain ⟨R, -, -, -, hR1, hR2, -, -, hline, -⟩ := _root_.GlobalTheory.KerReal.real_points D S T C
  have hdom : C.xB B ∈ C.X.dom := ((_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.1
  have hs := (GlobalTheory.Dict.hx_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even (C.xB B) hdom).1
  have hE := (zR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even (C.xB B) hdom).2.1
  have hψ := (_root_.GlobalTheory.FormMatch.forms_match D S T C).2.1
  have hlin : ∀ (a : WR C.X S.rank) (t : ℝ) (b : WR C.X S.rank),
      zR C.X C.idx (C.xB B) (a + t • b) = zR C.X C.idx (C.xB B) a + t • zR C.X C.idx (C.xB B) b := by
    intro a t b
    have h := (zRLin C.X C.idx (C.xB B) (n := S.rank)).map_add a (t • b)
    rw [map_smul] at h
    exact h
  have hsm : ∀ (t : ℝ) (b : WR C.X S.rank),
      zR C.X C.idx (C.xB B) (t • b) = t • zR C.X C.idx (C.xB B) b := fun t b =>
    (zRLin C.X C.idx (C.xB B) (n := S.rank)).map_smul t b
  have hT := hasDerivAt_translate C.X C.bas C.idx (C.xB B) hs Φ hΦ (C.zOf (C.xB B) w) u
  unfold Formalism.IndefR.Datum.dRho heisO
  refine (hT.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).deriv
  beta_reduce
  have hw' : w + lineAt C.θ τ z t =
      R (C.realPt w + t • (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank)) := by
    rw [hline, map_add (f := _), hR2 w hw]
  have hz : C.zOf (C.xB B)
      (R (C.realPt w + t • (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank))) =
      C.zOf (C.xB B) w + t • u := by
    unfold Ctx.zOf
    rw [(hR1 _).2, hlin, hu]
  rw [hw', hG _ (hR1 _).1, hz, hline, hψ w _ hw (hR1 _).1, (hR1 _).2, ← hE, hsm, ← hu]
  rfl

end GlobalTheory.Ker.HeisDeriv

theorem GlobalTheory.Ker.annih_crea_coord : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ (G : WO S T → ℂ) (Φ : (Fin S.rank → Fin C.g → ℂ) → ℂ), Differentiable ℝ Φ → (∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * Φ (C.zOf (C.xB B) w)) → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Fin S.rank → Fin C.g → ℂ), u = zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) → ∀ w, IsRealPt w → annih (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (fderiv ℝ Φ (C.zOf (C.xB B) w) u + I * fderiv ℝ Φ (C.zOf (C.xB B) w) (I • u)) ∧ crea (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (2 * ((-(π * ∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k))) * Φ (C.zOf (C.xB B) w) + (1 / 2 : ℂ) * (fderiv ℝ Φ (C.zOf (C.xB B) w) u - I * fderiv ℝ Φ (C.zOf (C.xB B) w) (I • u)))) := by
  intro D S T C B hB G Φ hΦ hG τ z u hu w hw
  have h1 := GlobalTheory.Ker.HeisDeriv.dRho_eq C B hB G Φ hΦ hG τ z u hu w hw
  have hJ : I • u = zR C.X C.idx (C.xB B)
      (Pi.single (C.m.e τ) (fun k a => conj ((cplxO 1 (C.sB B τ) z) a k)) : WR C.X S.rank) := by
    rw [hu]
    exact (((_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.2.2.1 τ z).symm
  have h2 := GlobalTheory.Ker.HeisDeriv.dRho_eq C B hB G Φ hΦ hG τ (cplxO 1 (C.sB B τ) z) (I • u) hJ w hw
  simp only [Pi.smul_apply, GlobalTheory.Ker.HeisDeriv.hx_smul_left, ← Finset.mul_sum] at h2
  unfold Formalism.IndefR.Datum.annih Formalism.IndefR.Datum.crea
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  constructor
  · linear_combination (-(gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (Real.pi : ℂ) *
      (∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k)) * Φ (C.zOf (C.xB B) w))) * I_sq
  · linear_combination (gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (Real.pi : ℂ) *
      (∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k)) * Φ (C.zOf (C.xB B) w)) * I_sq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsOpenStabilizerCompletedLatticeAdelicUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabOpen

noncomputable def stab {D : D7} (V : HSp D) (L : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) :
    Subgroup (GA D V) where
  carrier := {h | ∀ y, y ∈ L ↔ (finHom V h).1.mulVec y ∈ L}
  one_mem' := fun y => by rw [map_one, Units.val_one, Matrix.one_mulVec]
  mul_mem' := by
    intro a b ha hb y
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro a ha y
    rw [ha ((finHom V a⁻¹).1.mulVec y), Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel,
      map_one, Units.val_one, Matrix.one_mulVec]

theorem isOpen_stab_latHat : ∀ (D : D7) (V : HSp D), IsOpen {h : GA D V | ∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)} := by
  intro D V
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have e : Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) =
      GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
    rfl
  rw [e]
  have hn := GlobalTheory.LevelOpen.congr_mem_nhds D.host.F D.host.E V.rank _ hfg hsp 1 one_pos
  have hc := GlobalTheory.Member.continuous_finHom_val D V
  have h1 := hc.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [map_one, Units.val_one]; exact hn)
  have h2 := (hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds
    (by rw [Function.comp_apply, inv_one, map_one, Units.val_one]; exact hn)
  refine Subgroup.isOpen_of_mem_nhds (stab V (GlobalTheory.AdLat.hat D.host.F
    (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)))) (g := 1) ?_
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro k ⟨hk1, hk2⟩ y
  constructor
  · intro hy
    obtain ⟨w, hw, h⟩ := hk1 y hy
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy
  · intro hy
    obtain ⟨w, hw, h⟩ := hk2 _ hy
    rw [Function.comp_apply, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, Matrix.one_mulVec] at h
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy

end GlobalTheory.StabOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SectionsReadAsTranslatesAtScaledPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem reads_isUUOver_isVtOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (N : ℕ), Odd N → ∀ θ, A.Reads 1 y.s θ → (∀ a₁ a₂ : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a₁ = (2 : ℕ) • u) → (∃ u ∈ L, (N ^ 2 : ℕ) • a₂ = (2 : ℕ) • u) → ∀ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)), IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (A.ex (pv X idx x a₁)) (A.ex (pv X idx x a₂)) F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a₂)) (fock X bas idx x 1 (pv X idx x ((N : E) • a₁)) θ) ((N : ℂ) • z))) ∧ ∀ a : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a = (2 : ℕ) • u) → ∀ (t : (ptO Xo y.x) ⟶ Xo.univ.t.G) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), IsVtOver Xo.univ.t.G Xo.univ.t.PP N (fun t' => t' = A.ex (pv X idx x a)) y.s t F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a)) θ ((N : ℂ) • z)) := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL N hN θ hθ
  have hpv : ∀ (n : ℕ) (a : Fin r → E), pv X idx x ((n : E) • a) = (n : ℂ) • pv X idx x a := by
    intro n a
    rw [(hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx).2.2.2.2.1]
    funext j
    simp
  have hfk : ∀ (φ : (Fin g → ℂ) → ℂ) (a : Fin r → E),
      Dict.fock X bas idx x (N ^ 2) (pv X idx x a) (fun z => φ ((N : ℂ) • z)) =
        fun z => Dict.fock X bas idx x 1 (pv X idx x ((N : E) • a)) φ ((N : ℂ) • z) := by
    intro φ a
    rw [hpv]
    exact (fock_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx 1 φ).2.2.1 N _
  obtain ⟨Φ, he, -, hlat, -, -, hrd, hf⟩ := GlobalTheory.Dict.AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  have hχ : ∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1 := fun a ha =>
    (GlobalTheory.AnVal.chi_eq_sign E H Dw l Xo c y g _ e Φ a ha).1
  have htw : ∀ α₀ α s₁, α₀.IsGen → IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₀ →
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α
        (LB.pullGen Xo.univ.t.PP.L _ _ α₀ (snd (ptO Xo y.x) Xo.univ.t.G).left) →
      IsTwistPull Xo.univ.t.G Xo.univ.t.PP.L (mulT Xo.univ.t.G (ptO Xo y.x) N)
        (snd (ptO Xo y.x) Xo.univ.t.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α y.s s₁ →
      A.Reads ((N : ℤ) ^ 2) s₁ (fun z => θ ((N : ℂ) • z)) := by
    intro α₀ α s₁ hg hn hc ht
    exact (hrd _ _ _).1
      (GlobalTheory.T.normalisedPullbackMulN_reads_theta _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr N α₀ α y.s s₁ θ hg hn hc ht ((hrd _ _ _).2 hθ))
  have hsy : ∀ a : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a = (2 : ℕ) • u) →
      ∀ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x),
      SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) (A.ex (pv X idx x a)) U →
      ∀ (s s' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (φ : (Fin g → ℂ) → ℂ),
      IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) U s s' →
      A.Reads ((N : ℤ) ^ 2) s (fun z => φ ((N : ℂ) • z)) →
      A.Reads ((N : ℤ) ^ 2) s'
        (fun z => Dict.fock X bas idx x 1 (pv X idx x ((N : E) • a)) φ ((N : ℂ) • z)) := by
    rintro a ⟨u, hu, hau⟩ U hU s s' φ hA hs'
    have h2 : ((N ^ 2 : ℕ) : ℂ) • pv X idx x a = (2 : ℂ) • pv X idx x u := by
      have h3 := hpv 2 u
      rw [← hpv, Nat.cast_smul_eq_nsmul, hau, ← Nat.cast_smul_eq_nsmul E, h3]
      norm_num
    rw [← he] at hU
    have h4 := _root_.GlobalTheory.AnVal.rd_fock_of_symLift _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr hχ ((N : ℤ) ^ 2) (N ^ 2) U
      (pv X idx x a) (pv X idx x u) s s' _ hN.pow ((hlat _).2 ⟨u, hu, rfl⟩) h2 hU hA ((hrd _ _ _).2 hs')
    have h5 := hf (N ^ 2) (pv X idx x a) (fun z => φ ((N : ℂ) • z))
    rw [Nat.cast_pow, hfk] at h5
    rw [h5] at h4
    exact (hrd _ _ _).1 h4
  refine ⟨?_, ?_⟩
  · rintro a₁ a₂ h₁ h₂ F ⟨α₀, α, s₁, s₂, U₁, U₂, hg, hn, hc, ht, hU₁, hA₁, hU₂, hA₂⟩
    exact hsy a₂ h₂ U₂ hU₂ s₂ F _ hA₂ (hsy a₁ h₁ U₁ hU₁ s₁ s₂ _ hA₁ (htw α₀ α s₁ hg hn hc ht))
  · rintro a h t F ⟨t', α₀, α, s₁, U, -, rfl, hg, hn, hc, ht, hU, hA⟩
    exact hsy a h U hU s₁ F _ hA (htw α₀ α s₁ hg hn hc ht)

end GlobalTheory.Dict
end

