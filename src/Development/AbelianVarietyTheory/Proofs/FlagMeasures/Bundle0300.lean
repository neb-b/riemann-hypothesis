module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0289
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0288
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeGaussianSumOfLengthEqTsumStabilizerCosets
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantsScalarOnLowestKTypeCoefficients
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.CentreLow

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem smooth_comb {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') : SmoothOnG ε (fun h => f h + c * f' h) := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', e'⟩ := hf' g hg
  refine ⟨U ∩ U', fun h => F h + c * F' h, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (contDiffOn_const.mul (hF'.mono Set.inter_subset_right)), ?_⟩
  intro x hx hxJ
  simp only [e x hx.1 hxJ, e' x hx.2 hxJ]

theorem smooth_word {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    (w : List (Fin n × Fin n)) : SmoothOnG ε (Eword ε w f) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    have hc := complex_parts_mem_lie_algebra_holds n ε (Matrix.single p.1 p.2 1)
    exact smooth_comb Complex.I (rdSmooth_of right_derivative_extends n ε _ _ ih hc.1)
      (rdSmooth_of right_derivative_extends n ε _ _ ih hc.2.1)

theorem word_comb {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') (w : List (Fin n × Fin n)) :
    ∀ g, inUJ ε g → Eword ε w (fun h => f h + c * f' h) g = Eword ε w f g + c * Eword ε w f' g := by
  induction w with
  | nil => intro g _; rfl
  | cons p w ih =>
    intro g hg
    have hc := complex_parts_mem_lie_algebra_holds n ε (Matrix.single p.1 p.2 1)
    have h1 := Eword_congr ε ih [p] g hg
    have h2 := fun X hX => (right_derivative_linear n ε _ _ X X 0 c g (smooth_word hf w) (smooth_word hf' w) hX hX hg).2.2
    refine Eq.trans h1 ?_
    simp only [Eword, Eab, Ec, id, h2 _ hc.1, h2 _ hc.2.1]
    ring

theorem gelf_comb {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    gelf ε m (fun h => f h + c * f' h) g = gelf ε m f g + c * gelf ε m f' g := by
  simp only [gelf, word_comb c hf hf' _ g hg, Finset.sum_add_distrib, Finset.mul_sum]

theorem gelf_congr {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g, inUJ ε g → f g = f' g) (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    gelf ε m f g = gelf ε m f' g :=
  Finset.sum_congr rfl fun _ _ => Eword_congr ε h _ g hg

theorem centre_scalar_low : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∃ c : ℕ → ℂ, ∀ s ∈ lowKSub ε lam σ, ∀ u : H, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ) ∧ ∀ m, ∀ g ∈ UJset ε, gelf ε m (fun x => ⟪u, σ x s⟫_ℂ) g = c m * ⟪u, σ g s⟫_ℂ := by
  intro n ε lam H _ _ _ σ hσ hK
  obtain ⟨α, hα, hαc, hfix⟩ := _root_.GlobalTheory.exists_smooth_fix_lowKSub n ε lam H σ hσ hK
  have hD := fun (s : lowKSub ε lam σ) => _root_.GlobalTheory.DerivConv.derivConv n ε H σ α s hσ hα hαc (hfix s s.2)
  have hsm : ∀ (s : lowKSub ε lam σ) (u : H), SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ) := fun s => (hD s).1
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by simp [UJset, inUJ]
  have hone : ∀ v, σ 1 v = v := fun v => by rw [hσ.1.1]; rfl
  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, ∀ v, σ (a * b) v = σ a (σ b v) := fun a ha b hb v => by
    rw [hσ.1.2 a ha b hb]; rfl
  have hC : ∀ (m : ℕ) (s : lowKSub ε lam σ), ∃ s' : H, ∀ u, ∀ g ∈ UJset ε,
      gelf ε m (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g s'⟫_ℂ := by
    intro m s
    choose v hv using (hD s).2
    refine ⟨∑ a : Fin (m + 1) → Fin n, v (cycWord a), fun u g hg => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gelf, hv _ u g hg, map_sum, inner_sum]
  choose C hC using hC
  have hC1 : ∀ (m : ℕ) (s : lowKSub ε lam σ) (u : H),
      ⟪u, C m s⟫_ℂ = gelf ε m (fun x => ⟪u, σ x s⟫_ℂ) 1 := fun m s u => by rw [hC m s u 1 h1, hone]
  have hlin : ∀ (m : ℕ) (c : ℂ) (s t : lowKSub ε lam σ), C m (s + c • t) = C m s + c • C m t := by
    intro m c s t
    refine ext_inner_left ℂ fun u => ?_
    rw [inner_add_right, inner_smul_right, hC1, hC1, hC1, ← gelf_comb c (hsm s u) (hsm t u) m 1 h1]
    simp [inner_add_right, inner_smul_right]
  have h0 : ∀ m, C m 0 = 0 := fun m => by simpa using hlin m 1 0 0
  have key : ∀ m, ∃ c : ℂ, ∀ s : lowKSub ε lam σ, C m s = c • (s : H) := by
    intro m
    refine _root_.GlobalTheory.KMapInto.kMap_lowKSub_scalar n ε lam H σ hσ hK
      { toFun := C m
        map_add' := fun s t => by simpa using hlin m 1 s t
        map_smul' := fun c t => by simpa [h0] using hlin m c 0 t } ?_
    intro k hk s s' e
    have hkU : k ∈ UJset ε := (maximal_compact_facts n ε).1 k hk
    refine ext_inner_left ℂ fun u => ?_
    change ⟪u, C m s'⟫_ℂ = ⟪u, σ k (C m s)⟫_ℂ
    rw [hC1, ← hC m s u k hkU, ← Matrix.one_mul k,
      ← _root_.GlobalTheory.Dec.GelfAd.gelf_right n ε m _ k 1 (hsm s u) hkU h1]
    refine gelf_congr (fun g hg => ?_) m 1 h1
    rw [e, hmul g hg k hkU]
  choose c hc using key
  refine ⟨c, fun s hs u => ⟨hsm ⟨s, hs⟩ u, fun m g hg => ?_⟩⟩
  rw [hC m ⟨s, hs⟩ u g hg, hc, map_smul, inner_smul_right]

end GlobalTheory.CentreLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMassEqSumOverRationalGroupOrbits
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Unfold.massA_eq_sum_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → Function.Injective φ → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → ∀ d : Dat Z FP, massA F F' d = ∑' o : Quot (fun y y' : (∀ p, LocNG.Datum (FP p)) => ∃ h : ↥(FlagPairStabilizer F F'), (fun p => φ h p • y p) = y'), if (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite then (({h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • o.out p) = o.out}.encard : ℝ≥0∞))⁻¹ else 0 := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ _hinj _inst hmov d

  have huniq := (_root_.GlobalTheory.RatLocMove.rat_ext_moves D X Y u u' F F' w hw hG Z FP hB hR).1

  have key : ∀ (h : ↥(FlagPairStabilizer F F')) (y y' : Dat Z FP),
      RMoves h.1 y y' ↔ (fun p => φ h p • y p) = y' := by
    intro h y y'
    constructor
    · intro hm
      funext p
      obtain ⟨g', hg', hmv⟩ := hm p
      have he : g' = ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) :=
        (huniq h.1 p).unique hg' (hφ h p)
      subst he
      exact (hmov p (φ h p) (y p) (y' p)).1 hmv
    · intro he p
      exact ⟨_, hφ h p, (hmov p (φ h p) (y p) (y' p)).2 (congrFun he p)⟩

  have hrel : GRel (Z := Z) (FP := FP) F F' =
      (fun y y' : (∀ p, LocNG.Datum (FP p)) => ∃ h : ↥(FlagPairStabilizer F F'), (fun p => φ h p • y p) = y') := by
    funext y y'
    apply propext
    constructor
    · rintro ⟨h, hh, hm⟩
      exact ⟨⟨h, (mem_H0sub F F' h).2 hh⟩, (key ⟨h, (mem_H0sub F F' h).2 hh⟩ y y').1 hm⟩
    · rintro ⟨h, hh⟩
      exact ⟨h.1, (mem_H0sub F F' h.1).1 h.2, (key h y y').2 hh⟩

  have hstab : ∀ y : Dat Z FP, (stabY F F' y).encard =
      {h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • y p) = y}.encard := by
    intro y
    have hs : stabY F F' y = Subtype.val '' {h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • y p) = y} := by
      ext g
      constructor
      · rintro ⟨hg, hm⟩
        exact ⟨⟨g, (mem_H0sub F F' g).2 hg⟩, (key ⟨g, (mem_H0sub F F' g).2 hg⟩ y y).1 hm, rfl⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨(mem_H0sub F F' h.1).1 h.2, (key h y y).2 hh⟩
    rw [hs, Subtype.val_injective.encard_image]
  rw [massA, hrel]
  refine tsum_congr fun o => ?_

  have hin : InGen d o.out ↔
      (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite := by
    unfold InGen
    refine and_congr (forall_congr' fun p => ?_) Iff.rfl
    constructor
    · rintro ⟨g, hg, hm⟩
      exact ⟨⟨g, hg⟩, (hmov p ⟨g, hg⟩ (d p) (o.out p)).1 hm⟩
    · rintro ⟨g, hg⟩
      exact ⟨g.1, g.2, (hmov p g (d p) (o.out p)).2 hg⟩
  by_cases hc : (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite
  · rw [if_pos (hin.2 hc), if_pos hc, hstab]
  · rw [if_neg (mt hin.1 hc), if_neg hc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerPreimageEqOfLocalInnerLatticeEq
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.LsubG

variable {D : D7}

theorem exists_proj (X : Submodule D.host.E (VS D).V) :
    ∃ Q : (VS D).V →ₗ[D.host.E] (VS D).V, (∀ x ∈ X, Q x = 0) ∧ (∀ v, v - Q v ∈ X) ∧ ∀ v, Q (Q v) = Q v := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl X
  have hC' : IsCompl C X := hC.symm
  refine ⟨C.projection X hC', fun x hx => (Submodule.projection_apply_eq_zero_iff hC').2 hx, fun v => ?_, fun v => ?_⟩
  · rw [← Submodule.projection_eq_self_sub_projection hC']
    exact Submodule.projection_apply_mem _ _
  · exact Submodule.projection_apply_of_mem_left hC' (Submodule.projection_apply_mem _ _)

def endP (p : PlF D) (Q : (VS D).V →ₗ[D.host.E] (VS D).V) : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p :=
  Fintype.linearCombination (D.s.atP p).Ep (fun i => baseChange₂ D p (Q ((VS D).frame i)))

theorem bcP_endP (p : PlF D) (Q : (VS D).V →ₗ[D.host.E] (VS D).V) (x : (VS D).V) :
    endP p Q (baseChange₂ D p x) = baseChange₂ D p (Q x) := by
  rw [endP, Fintype.linearCombination_apply]
  conv_rhs => rw [← (VS D).frame.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, baseChange_smul₂]
  rfl

theorem endP_latP (Z : LocDat D) (p : PlF D) (Q : (VS D).V →ₗ[D.host.E] (VS D).V) (Λ : LV D) {y : Vp D p}
    (hy : y ∈ lattice₂ D Z.M p Λ) : endP p Q y ∈ lattice₂ D Z.M p (Λ.map (Q.restrictScalars (𝓞 D.host.E))) := by
  refine Submodule.span_induction (p := fun y _ => endP p Q y ∈ lattice₂ D Z.M p (Λ.map (Q.restrictScalars (𝓞 D.host.E))))
    ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨x, hx, rfl⟩
    rw [bcP_endP]
    exact Submodule.subset_span ⟨Q x, Submodule.mem_map_of_mem hx, rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    have e : endP p Q (c • a) = c • endP p Q a := by
      rw [Subring.smul_def, Subring.smul_def, map_smul]
    rw [e]; exact Submodule.smul_mem _ c ha

theorem localLattice_mono' (Z : LocDat D) (p : PlF D) {Λ Λ' : LV D} (h : Λ ≤ Λ') : lattice₂ D Z.M p Λ ≤ lattice₂ D Z.M p Λ' :=
  Submodule.span_mono (Set.image_mono h)

theorem mem_of_local (Z : LocDat D) (Γ : LV D) (hΓ : Submodule.IsLattice D.host.E Γ) (x : (VS D).V)
    (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Z.M p Γ) : x ∈ Γ := by
  let X := Submodule.span D.host.E (Γ : Set (VS D).V)
  obtain ⟨Q, hQX, hQv, hQQ⟩ := exists_proj X
  let B : LV D := Submodule.span (𝓞 D.host.E) (Set.range (VS D).frame)
  let Λ := Γ ⊔ B.map (Q.restrictScalars (𝓞 D.host.E))
  have hΓΛ : Γ ≤ Λ := le_sup_left
  have hB : B.FG := Submodule.fg_span (Set.finite_range _)
  have hΛ : Submodule.IsLattice D.host.E Λ :=
    Submodule.IsLattice.of_fg D.host.E (hΓ.fg.sup (hB.map _))
  have hspan : Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ := by
    apply top_unique
    rw [← (VS D).frame.span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    change (VS D).frame i ∈ Submodule.span D.host.E (Λ : Set (VS D).V)
    have hdiff := Submodule.span_mono (show (Γ : Set (VS D).V) ⊆ Λ from hΓΛ) (hQv ((VS D).frame i))
    have hi : (VS D).frame i ∈ B := Submodule.subset_span (Set.mem_range_self i)
    have hQi : Q ((VS D).frame i) ∈ Λ :=
      Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := Q.restrictScalars (𝓞 D.host.E)) hi)
    simpa only [sub_add_cancel] using (Submodule.span D.host.E (Λ : Set (VS D).V)).add_mem
      hdiff (Submodule.subset_span hQi)
  have hfull : Submodule.IsFullLattice D.host.E (LatLoc.cL Λ) := by
    refine { toIsLattice := LatLoc.isLattice_map (LatLoc.cE D) Λ hΛ, span_eq_top := ?_ }
    change Submodule.span D.host.E ((LatLoc.cE D).toLinearMap '' (Λ : Set (VS D).V)) = ⊤
    rw [← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]
  have hrec := (_root_.GlobalTheory.HL.PlacesRec.lattice_local
    (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ) hfull).1
  have hx : x ∈ Λ := by
    have hmem := (hrec (LatLoc.cE D x)).2 fun p => by
      rw [← LatLoc.baseChange_eq, ← LatLoc.localLattice_eq]
      exact localLattice_mono' Z p hΓΛ (h p)
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hmem
    exact (show y = x from (LatLoc.cE D).injective hyx) ▸ hy
  have hmap : Γ.map (Q.restrictScalars (𝓞 D.host.E)) = ⊥ := by
    apply (Submodule.eq_bot_iff _).2
    rintro _ ⟨y, hy, rfl⟩
    exact hQX y (Submodule.subset_span hy)
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  let p : PlF D := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField D.host.F)⟩
  have hbc := endP_latP Z p Q Γ (h p)
  rw [hmap, lattice₂, Submodule.bot_coe, Set.image_singleton, map_zero, Submodule.span_zero_singleton,
    Submodule.mem_bot, bcP_endP, ← map_zero (baseChange₂ D p)] at hbc
  have hQx : Q x = 0 := by
    refine (VS D).frame.ext_elem fun i => (D.s.atP p).ιE.injective ?_
    exact congrFun hbc i
  obtain ⟨y, hy, _, ⟨z, _, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
  change Q (y + Q z) = 0 at hQx
  rw [map_add, hQX y (Submodule.subset_span hy), hQQ, zero_add] at hQx
  simpa only [LinearMap.restrictScalars_apply, hQx, add_zero] using hy

theorem herm_smul_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (c : E) (u w : V) : H.h u (c • w) = M.L.cj c * H.h u w := by
  rw [H.h_herm (c • w) u, H.h_smul_left, map_mul, ← H.h_herm w u]

theorem herm_span_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (u : V) (S : Set V) (hS : ∀ s ∈ S, H.h u s = 0) :
    ∀ w ∈ Submodule.span E S, H.h u w = 0 := by
  intro w hw
  refine Submodule.span_induction (p := fun w _ => H.h u w = 0) hS ?_ ?_ ?_ hw
  · rw [H.h_herm 0 u, H.h_zero_left, map_zero]
  · intro a b _ _ ha hb
    rw [H.h_herm (a + b) u, H.h_add_left, map_add (f := _), ← H.h_herm a u, ← H.h_herm b u, ha, hb, add_zero]
  · intro c a _ ha
    rw [herm_smul_right, ha, mul_zero]

theorem X_iso {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) {x : (VS D).V} (hx : x ∈ Xsp G) :
    x ∈ orth (VS D) (Xsp G) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro y hy
  have hgen : ∀ b, (VS D).hT y (G.fl.e b) = 0 := by
    intro b
    refine Submodule.span_induction (p := fun y _ => (VS D).hT y (G.fl.e b) = 0) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨a, rfl⟩; exact G.fl.e_iso a b
    · simp
    · intro a c _ _ ha hc; simp [ha, hc]
    · intro c a _ ha; simp [ha]
  refine Submodule.span_induction (p := fun x _ => (VS D).hT y x = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨b, rfl⟩; exact hgen b
  · simp
  · intro a c _ _ ha hc; simp [ha, hc]
  · intro c a _ ha; simp [ha]

set_option maxHeartbeats 1000000 in
theorem lsub_le (Z : LocDat D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (f : ∀ p : PlF D, Fin (D.R.rS + 1) → Vp D p)
    (hf : ∀ p, f p = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) (Λ₁ Λ₂ : LV D)
    (h₂ : Submodule.IsLattice D.host.E Λ₂)
    (hL : ∀ p, (locH Z p).Lset (lattice₂ D Z.M p Λ₁) (f p) ⊆ (locH Z p).Lset (lattice₂ D Z.M p Λ₂) (f p)) :
    Lsub Λ₁ G ≤ Lsub Λ₂ G := by
  obtain ⟨Q, hQX, hQv, hQQ⟩ := exists_proj (Xsp G)
  set Γ : LV D := Λ₂ ⊔ Λ₂.map (Q.restrictScalars (𝓞 D.host.E)) with hΓdef
  have hΓ : Submodule.IsLattice D.host.E Γ :=
    Submodule.IsLattice.of_fg D.host.E (h₂.fg.sup (h₂.fg.map _))
  intro v hv
  have hvo : v ∈ orth (VS D) (Xsp G) := hv.2
  obtain ⟨l, hl, x, hx, rfl⟩ := Submodule.mem_sup.1 hv.1
  have hlo : l ∈ orth (VS D) (Xsp G) := hl.2
  have hloc : ∀ p, baseChange₂ D p (Q (l + x)) ∈ lattice₂ D Z.M p Γ := by
    intro p
    have hXQ : ∀ w ∈ (locH Z p).X (f p), endP p Q w = 0 := by
      intro w hw
      refine Submodule.span_induction (p := fun w _ => endP p Q w = 0) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨a, rfl⟩
        rw [hf p]
        simp only
        rw [map_smul, bcP_endP, hQX _ (Submodule.subset_span ⟨a, by simp [frame, FlagG.fvec]⟩), map_zero, smul_zero]
      · exact map_zero _
      · intro a b _ _ ha hb; rw [map_add (f := _), ha, hb, add_zero]
      · intro c a _ ha; rw [map_smul, ha, smul_zero]
    have hperp : baseChange₂ D p l ∈ (locH Z p).perp ((locH Z p).X (f p)) := by
      intro w hw
      refine herm_span_right (locH Z p) (baseChange₂ D p l) _ ?_ w hw
      rintro _ ⟨a, rfl⟩
      rw [hf p]
      simp only
      rw [herm_smul_right]
      have e0 : (locH Z p).h (baseChange₂ D p l) (baseChange₂ D p (frame G a.castSucc)) = 0 := by
        show LocFacts₂ Z.M p (baseChange₂ D p l) (baseChange₂ D p (frame G a.castSucc)) = 0
        rw [baseChangeAt_form Z.M p (Z.hcj p), brS]
        have hmem : frame G a.castSucc ∈ Xsp G := Submodule.subset_span ⟨a, by simp [frame, FlagG.fvec]⟩
        have := hlo
        simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at this
        rw [this _ hmem, map_zero]
      rw [e0, mul_zero]
    obtain ⟨y, hy, hyw⟩ := hL p ⟨⟨baseChange₂ D p l, hperp⟩, Submodule.subset_span ⟨l, hl.1, rfl⟩, rfl⟩
    have hdiff : ((y : Vp D p) - baseChange₂ D p l) ∈ (locH Z p).X (f p) := by
      have := (Submodule.Quotient.eq _).1 hyw
      simpa using this
    have e : endP p Q (baseChange₂ D p l) = endP p Q y := by
      have := hXQ _ hdiff
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    rw [← bcP_endP, map_add (f := _), map_add (f := _), e, bcP_endP p Q x, hQX x hx, map_zero, add_zero]
    exact localLattice_mono' Z p (le_sup_right : Λ₂.map (Q.restrictScalars (𝓞 D.host.E)) ≤ Γ) (endP_latP Z p Q Λ₂ hy)
  have hmem : Q (l + x) ∈ Γ := mem_of_local Z Γ hΓ _ hloc
  obtain ⟨a, ha, b', hb', hab⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hb'
  have hQab : Q a + Q b = Q (l + x) := by
    have := congrArg Q hab
    simp only [LinearMap.restrictScalars_apply, map_add (f := _), hQQ] at this
    rw [map_add Q l x]
    exact this
  have h2 : Q (l + x - (a + b)) = 0 := by
    rw [map_sub Q, map_add Q a b, hQab, sub_self]
  have hc : l + x - (a + b) ∈ Xsp G := by
    have h1 := hQv (l + x - (a + b))
    rw [h2, sub_zero] at h1
    exact h1
  have hco : a + b ∈ orth (VS D) (Xsp G) := by
    have : a + b = (l + x) - (l + x - (a + b)) := by abel
    rw [this]
    exact Submodule.sub_mem _ hvo (X_iso G hc)
  refine ⟨Submodule.mem_sup.2 ⟨a + b, ⟨Submodule.add_mem _ ha hb, hco⟩, l + x - (a + b), hc, by abel⟩, hvo⟩

theorem lsub_eq_of_local : ∀ (D : D7) (Z : LocDat D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) (Fr : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (Fr p).f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → (∀ p, (locH Z p).Lset (lattice₂ D Z.M p Λ₁) (Fr p).f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) (Fr p).f) → Lsub Λ₁ G = Lsub Λ₂ G := by
  intro D Z T G Fr hFr Λ₁ Λ₂ h₁ h₂ hL
  exact le_antisymm
    (lsub_le Z G (fun p => (Fr p).f) hFr Λ₁ Λ₂ h₂ fun p => (hL p).le)
    (lsub_le Z G (fun p => (Fr p).f) hFr Λ₂ Λ₁ h₁ fun p => (hL p).ge)

end GlobalTheory.Unfold.LsubG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryTransportsDiscriminantModule
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mass.Transp.discModule_transport : ∀ (K V V' : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (e : V ≃ₗ[K] V'), (∀ x y, h' (e x) (e y) = h x y) → ∀ (L : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)), GlobalTheory.Mass.IsIntLat h' (GlobalTheory.Mass.Transp.img e L) → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L)) ⧸ (GlobalTheory.Mass.Transp.img e L).comap (Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L)).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ I)) → GlobalTheory.Mass.IsIntLat h L ∧ Nonempty ((↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ I)) := by
  intro K V V' _ _ _ _ _ _ _ _ _ _ _ h h' e he L I hI hQ
  have hL : GlobalTheory.Mass.IsIntLat h L := by
    have := GlobalTheory.Mass.Transp.intLat_img e.symm (GlobalTheory.Mass.Transp.symm_isom e he) _ hI
    rwa [GlobalTheory.Mass.Transp.img_symm_img] at this
  refine ⟨hL, ?_⟩
  obtain ⟨q⟩ := hQ
  set D := Formalism.HermitianLatticesTheory.dual h L with hDdef
  set D' := Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L) with hD'def
  have hD : D' = GlobalTheory.Mass.Transp.img e D := GlobalTheory.Mass.Transp.dual_img e he L
  have hmem : ∀ x : V, x ∈ D → e x ∈ D' := by
    intro x hx; rw [hD, GlobalTheory.Mass.Transp.mem_img]; simpa using hx
  have hmem' : ∀ y : V', y ∈ D' → e.symm y ∈ D := by
    intro y hy; rw [hD, GlobalTheory.Mass.Transp.mem_img] at hy; exact hy
  let f : D ≃ₗ[𝓞 K] D' :=
    { toFun := fun x => ⟨e x, hmem x x.2⟩
      invFun := fun y => ⟨e.symm y, hmem' y y.2⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by
        ext
        simp only [SetLike.val_smul, RingHom.id_apply]
        exact (e.toLinearMap.restrictScalars (𝓞 K)).map_smul r x
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp }
  have hf : (L.comap D.subtype).map (f : D →ₗ[𝓞 K] D') = (GlobalTheory.Mass.Transp.img e L).comap D'.subtype := by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    rw [GlobalTheory.Mass.Transp.mem_img]
    constructor
    · rintro ⟨⟨x, hx⟩, hxL, hxy⟩
      have : (f ⟨x, hx⟩ : V') = y := congrArg Subtype.val hxy
      simp only [f, LinearEquiv.coe_mk] at this
      rw [← this]; simpa using hxL
    · intro hyL
      refine ⟨⟨e.symm y, hmem' y hy⟩, hyL, ?_⟩
      ext; simp [f]
  exact ⟨(Submodule.Quotient.equiv _ _ f hf).trans q⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeGaussianSumOfLengthEqTsumStabilizerCosetsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeGaussianSumOfLength_eq_tsum_stabilizer_cosets : ∀ (I : AutInst) (s : Bool) (x : Fin I.n → I.E), star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s → ∃ (ι : Type) (_ : Countable ι) (r : ι → I.GA), (∀ i, r i ∈ I.GFset) ∧ (∀ γ ∈ I.GFset, ∃! i, γ * (r i)⁻¹ ∈ stabF I x) ∧ ∀ g, gaussSum I (sgn I.E s) g = ∑' i, gaussAt I x (r i * g) := by
  first | exact @GlobalTheory.StabCosets.gaussSum_cosets | exact GlobalTheory.StabCosets.gaussSum_cosets | (intros; apply GlobalTheory.StabCosets.gaussSum_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusPropertiesStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviFactorInverseModulus_properties : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), Measurable (dlt (ε := ε) j W) ∧ (∀ l ∈ maxK ε ∩ flagM ε W, ∀ m ∈ flagM ε W, dlt j W (m * l) = dlt j W m) ∧ ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ ∀ m ∈ flagM ε W, nrm (uMat m - 1) < t → dlt j W m ≤ ENNReal.ofReal (1 + η) ∧ 1 ≤ ENNReal.ofReal (1 + η) * dlt j W m := by
  first | exact @GlobalTheory.IwDelta.dlt_props | exact GlobalTheory.IwDelta.dlt_props | (intros; apply GlobalTheory.IwDelta.dlt_props <;> assumption)
end

