module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuesMemOfLocal
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TwoRunDatumBoundUnitAtIndefinitePoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0583
public import Formalism.PieriBlockIdeals.PieriColumnMinors.CorollaryOfParamsSevenLinkageAlt
public import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0063
public import Formalism.LocalRingCardinality.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnipotentEmbeddingsExist
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LinWCoords

theorem exists_split_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v),
    ∃ uT uM : Matrix (Fin a) (Fin (a + a')) (Fv F v) →+ Matrix (Fin a) (Fin (a + a')) (AE F E),
      (∀ Y, At (evFin F v) (uT Y) ∧ (uT Y).map (piW (t.comp σ)) = 0 ∧ (uT Y).map (piW t) = Y) ∧
      (∀ z, At (evFin F v) (uM z) ∧ (uM z).map (piW t) = 0 ∧ GlobalTheory.LinWAt.coW G t (uM z) = z) ∧
      (∀ u, At (evFin F v) u → ∃ Y z, u = uT Y + uM z) ∧
      (∀ x u, At (evFin F v) x → At (evFin F v) u →
        evFin F v (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) x u) =
          ∑ i, ∑ j, (x.map (piW t)) i j * GlobalTheory.LinWAt.coW G t u i j -
            ∑ i, ∑ j, GlobalTheory.LinWAt.coW G t x i j * (u.map (piW t)) i j) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v t
  have hcm := hTr.base.cm
  have hP : IsUnit (G.V.J.map t).det :=
    GlobalTheory.LinBarCoords.det_map_isUnit B G.V.J 1 _ _ one_ne_zero (fun w => by rw [one_smul]; exact hTr.geo.hV.sig w) v t
  have hQ : IsUnit ((G.W.J.map t)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact GlobalTheory.LinBarCoords.det_map_isUnit B G.W.J Complex.I _ _ Complex.I_ne_zero hTr.geo.hW.sig v t
  set P := G.V.J.map t with hPdef
  set Q := (G.W.J.map t)ᵀ with hQdef
  let L := GlobalTheory.LinBarCoords.liftM σ hcm (m := Fin a) (n := Fin (a + a')) v t
  let uT : Matrix (Fin a) (Fin (a + a')) (Fv F v) →+ Matrix (Fin a) (Fin (a + a')) (AE F E) :=
    AddMonoidHom.mk' (fun Y => L (Y, 0)) (fun Y Y' => by rw [← map_add (f := _), Prod.mk_add_mk, add_zero])
  let uM : Matrix (Fin a) (Fin (a + a')) (Fv F v) →+ Matrix (Fin a) (Fin (a + a')) (AE F E) :=
    AddMonoidHom.mk' (fun z => L (0, -(P⁻¹ * z * Q⁻¹))) (fun z z' => by
      rw [Matrix.mul_add, Matrix.add_mul, neg_add, ← map_add (f := _), Prod.mk_add_mk, add_zero])
  have hco : ∀ u, GlobalTheory.LinWAt.coW G t u = -(P * u.map (piW (t.comp σ)) * Q) := fun u => by
    simp [GlobalTheory.LinWAt.coW, hPdef, hQdef]
  have hTc : ∀ Y, (uT Y).map (piW (t.comp σ)) = 0 := fun Y => GlobalTheory.LinBarCoords.liftM_snd σ hcm v t _
  have hTt : ∀ Y, (uT Y).map (piW t) = Y := fun Y => GlobalTheory.LinBarCoords.liftM_fst σ hcm v t _
  have hMc : ∀ z, (uM z).map (piW (t.comp σ)) = -(P⁻¹ * z * Q⁻¹) := fun z => GlobalTheory.LinBarCoords.liftM_snd σ hcm v t _
  have hMt : ∀ z, (uM z).map (piW t) = 0 := fun z => GlobalTheory.LinBarCoords.liftM_fst σ hcm v t _
  have hTa : ∀ Y, At (evFin F v) (uT Y) := fun Y => GlobalTheory.LinBarCoords.liftM_at σ hcm v t _
  have hMa : ∀ z, At (evFin F v) (uM z) := fun z => GlobalTheory.LinBarCoords.liftM_at σ hcm v t _
  refine ⟨uT, uM, fun Y => ⟨hTa Y, hTc Y, hTt Y⟩, fun z => ⟨hMa z, hMt z, ?_⟩, fun u hu => ?_, fun x u hx hu => ?_⟩
  · have e1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
    have e2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQ
    rw [hco, hMc, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    simp only [← Matrix.mul_assoc, e1, Matrix.one_mul]
    simp only [Matrix.mul_assoc, e2, Matrix.mul_one]
  · refine ⟨u.map (piW t), GlobalTheory.LinWAt.coW G t u, ?_⟩
    have hd : At (evFin F v) (u - (uT (u.map (piW t)) + uM (GlobalTheory.LinWAt.coW G t u))) := by
      intro c hc
      rw [smul_sub, smul_add, hu c hc, hTa _ c hc, hMa _ c hc, add_zero, sub_zero]
    refine (sub_eq_zero.1 (GlobalTheory.LinBarCoords.eq_zero_of_at σ hcm v t hd ?_ ?_))
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTt, hMt, add_zero, sub_self]
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTc, hMc, zero_add, hco, Matrix.mul_neg, Matrix.neg_mul,
        neg_neg, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, sub_self]
  · have h := GlobalTheory.T.local_lattice_hermitian_skew hcm v t G.V.J G.W.J hTr.geo.hV.herm hTr.geo.hW.skew x u hx
    dsimp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM] at h
    rw [hco, hco]
    exact h

end GlobalTheory.LinWCoords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGroupOrderBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

noncomputable section

namespace GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_GL_zmod_le (r q : ℕ) (hq : q ≠ 0) :
    Nat.card (GL (Fin r) (ZMod q)) ≤ q ^ (r * r) := by
  haveI : NeZero q := ⟨hq⟩
  calc Nat.card (GL (Fin r) (ZMod q)) ≤ Nat.card (Matrix (Fin r) (Fin r) (ZMod q)) :=
        Nat.card_le_card_of_injective (fun u => (u : Matrix (Fin r) (Fin r) (ZMod q))) (fun a b h => Units.ext h)
    _ = q ^ (r * r) := by
        rw [Nat.card_eq_fintype_card]
        show Fintype.card (Fin r → Fin r → ZMod q) = q ^ (r * r)
        rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← pow_mul]

end GlobalTheory.CovTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealsMeetingSubspaceCover
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpCover

private theorem latD_of {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N)
    (lam : ι → ℕ → ℕ) (y : NablaT (PadicAlgCl l) N lam)
    (h : ∃ x ∈ tensSub (deltaIn F.O N lam), GlobalTheory.LatBC.bc F.emb N lam x = y) : y ∈ F.latD lam := by
  obtain ⟨x, ⟨z, rfl⟩, rfl⟩ := h
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [LinearMap.map_smul, PiTensorProduct.map_tprod, LinearMap.map_smulₛₗ, GlobalTheory.LatBC.bc_tprod]
    exact AddSubgroup.subset_closure ⟨r, fun τ => GlobalTheory.LatBC.dwMap F.emb N _ (m τ),
      fun τ => ⟨((m τ : Formalism.GradedWeylDivisibility.dualWeyl F.O N N (res N (lam τ))) : MvPolynomial (Fin N × Fin N) F.O), (m τ).2, rfl⟩, rfl⟩
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem ha hb

end GlobalTheory.ExpCover

namespace GlobalTheory.ExpCover

section Glue

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type}
  (B : BlockDat K G0 Pl0) (ℓ : Lvl K G0) (Z : Submodule K B.S.Forms)

private theorem toF_coe (z : Fin (B.dZ ℓ Z) → K) :
    ((B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) = B.S.I ((B.fE ℓ Z).mulVec z) := by
  simp [BlockDat.toF, BlockDat.fE, CSD.I, Matrix.mulVec_mulVec]

private theorem toF_mem (z : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z z ∈ Z := by
  have h1 : (B.zE ℓ Z).mulVec z ∈ B.Z0 ℓ Z := by
    rw [BlockDat.zE, subE_mulVec]; exact Submodule.coe_mem _
  have h2 : (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec z) ∈ B.coord Z := h1
  obtain ⟨f, hf, hfe⟩ := Submodule.mem_map.1 h2
  have : B.toF ℓ Z z = f := by
    simp only [BlockDat.toF, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply]
    rw [← hfe]; simp
  rw [this]; exact hf

private theorem mem_cutZ (z : Fin (B.dZ ℓ Z) → K) :
    z ∈ B.cutZ ℓ Z ↔ ∀ c, ((B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) c ∈ B.S.Nab c := by
  rw [toF_coe]
  simp [BlockDat.cutZ, Formalism.DivisionValues.cutLat, CSD.nabLat, Formalism.DivisionValues.valLatF, Submodule.mem_pi]

private theorem mem_delZ (z : Fin (B.dZ ℓ Z) → K) :
    z ∈ B.delZ ℓ Z ↔ ∀ c, ((B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) c ∈ B.S.Del c := by
  rw [toF_coe]
  simp [BlockDat.delZ, Formalism.DivisionValues.cutLat, CSD.delLat, Formalism.DivisionValues.valLatF, Submodule.mem_pi]

private theorem final_step (w : HeightOneSpectrum (𝓞 K)) (L : 𝓞 K) (z : Fin (B.dZ ℓ Z) → K)
    (h : ∃ s : 𝓞 K, s ∉ w.asIdeal ∧
      ∀ c, s • (((algebraMap (𝓞 K) K L) • B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) c ∈ B.S.Del c) :
    L • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (B.delZ ℓ Z) := by
  obtain ⟨s, hs, hc⟩ := h
  refine ⟨s, hs, ?_⟩
  rw [mem_delZ]
  intro c
  have e : B.toF ℓ Z (s • L • z) = (algebraMap (𝓞 K) K s) • (algebraMap (𝓞 K) K L) • B.toF ℓ Z z := by
    rw [← map_smul, ← map_smul, algebraMap_smul, algebraMap_smul]
  rw [e]
  simpa [algebraMap_smul] using hc c

end Glue

end GlobalTheory.ExpCover

namespace GlobalTheory.ExpCover

private theorem isForm_of_span {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)
    (A : Set (F.G → NablaT (PadicAlgCl l) N lam)) (hA : ∀ f ∈ A, F.IsForm lam f) :
    ∀ f ∈ Submodule.span (PadicAlgCl l) A, F.IsForm lam f := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf => exact hA f hf
  | zero => exact ⟨fun _ _ _ => rfl, fun κ g => by rw [Pi.zero_apply, Pi.zero_apply, map_zero, smul_zero]⟩
  | add f f' _ _ h h' =>
    refine ⟨fun γ hγ g => by rw [Pi.add_apply, Pi.add_apply, h.1 γ hγ, h'.1 γ hγ], fun κ g => ?_⟩
    rw [Pi.add_apply, Pi.add_apply, map_add (f := _), smul_add, h.2, h'.2]
  | smul a f _ h =>
    refine ⟨fun γ hγ g => by rw [Pi.smul_apply, Pi.smul_apply, h.1 γ hγ], fun κ g => ?_⟩
    rw [Pi.smul_apply, Pi.smul_apply, map_smul, smul_comm, h.2]

private theorem span_stable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
    {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type} {B : BlockDat K G0 Pl0}
    {w : HeightOneSpectrum (𝓞 K)} (R : Reads F lam B w) (Z : Submodule K B.S.Forms) (hZ : ∀ i, Z ≤ Z.comap (B.op i)) (i : F.I) :
    ∀ u ∈ Submodule.span (PadicAlgCl l) (R.rd '' Z),
      transOp (F.emb (F.cst i)) (F.tr i) u ∈ Submodule.span (PadicAlgCl l) (R.rd '' Z) := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨f, hf, rfl⟩ := hu
    exact Submodule.subset_span ⟨B.op (R.ix i) f, hZ (R.ix i) hf, funext fun g => R.hecke i f g⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h h' => rw [map_add (f := _)]; exact Submodule.add_mem _ h h'
  | smul a _ _ h => rw [map_smul]; exact Submodule.smul_mem _ a h

private theorem forms_fin : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ)
    (jK : F.K →* alg F.O N lam), F.Ok → Module.Finite F.O (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam)) := by
  intro l _ ι _ _ N F lam jK hF
  haveI : Module.Finite F.O (NablaT F.O N lam) := GlobalTheory.NablaFin.nablaT_finite F.O N ι lam
  obtain ⟨S, hS⟩ := hF.classes
  haveI : Finite (Formalism.UG.ClassSet F.Γ F.K) := by
    refine Finite.of_surjective (fun s : S => (DoubleCoset.mk F.Γ F.K (s : F.G) : Formalism.UG.ClassSet F.Γ F.K)) ?_
    intro c
    obtain ⟨γ, hγ, s, hs, κ, hκ, e⟩ := hS (Quotient.out c)
    refine ⟨⟨s, hs⟩, ?_⟩
    show DoubleCoset.mk F.Γ F.K s = c
    rw [← DoubleCoset.out_eq' c]
    exact (@DoubleCoset.eq _ _ F.Γ F.K s _).2 ⟨γ, hγ, κ, hκ, e⟩
  exact Formalism.UG.P.automorphic_forms_level_finite_holds F.G F.Γ F.K F.O (NablaT F.O N lam) _ ‹_›

private theorem emb_norm : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok →
    (∀ c, ‖F.emb c‖ ≤ 1) ∧ ∀ c, ‖F.emb c‖ = 1 → IsUnit c := by
  intro l _ ι N F hF
  obtain ⟨hinj, L, _, hL⟩ := hF.ring
  have hmem : ∀ c, F.emb c ∈ L ∧ ‖F.emb c‖ ≤ 1 := by
    intro c
    have : F.emb c ∈ Set.range F.emb := ⟨c, rfl⟩
    rw [hL] at this
    exact this
  refine ⟨fun c => (hmem c).2, fun c hc => ?_⟩
  have hne : F.emb c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hinvL : (F.emb c)⁻¹ ∈ L := inv_mem (hmem c).1
  have hinvn : ‖(F.emb c)⁻¹‖ ≤ 1 := by rw [norm_inv, hc, inv_one]
  have : (F.emb c)⁻¹ ∈ Set.range F.emb := by rw [hL]; exact ⟨hinvL, hinvn⟩
  obtain ⟨d, hd⟩ := this
  have hcd : c * d = 1 := hinj (by rw [map_mul, map_one, hd, mul_inv_cancel₀ hne])
  exact IsUnit.of_mul_eq_one d hcd

private theorem form_lift : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) (b : NablaT F.O N lam →ₛₗ[F.emb] NablaT (PadicAlgCl l) N lam), Function.Injective b → (∀ g x, b (grp F.O N lam g x) = grp (PadicAlgCl l) N lam (fun τ => Matrix.GeneralLinearGroup.map F.emb (g τ)) (b x)) → F.IsJ lam jK → ∀ f : F.G → NablaT (PadicAlgCl l) N lam, F.IsForm lam f → (∀ g, ∃ y, b y = f g) → ∃ x : Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam), ∀ g, b ((x : F.G → NablaT F.O N lam) g) = f g := by
  intro l _ ι _ _ N F lam jK b hb hgrp hJ f hf hex
  choose x hx using hex
  refine ⟨⟨x, ?_⟩, hx⟩
  intro γ g κ
  apply hb
  rw [hx]
  change f _ = b ((jK κ⁻¹ : alg F.O N lam) • x g)
  have e1 : (jK κ⁻¹ : alg F.O N lam) • x g = ((F.chi κ⁻¹ : F.Oˣ) : F.O) • grp F.O N lam (F.kap κ⁻¹) (x g) := by
    rw [hJ κ⁻¹, smul_assoc]
    rfl
  rw [e1, LinearMap.map_smulₛₗ, hgrp, hx]
  have h2 := hf.2 κ⁻¹ (g * κ)
  simp only [Subgroup.coe_inv, mul_inv_cancel_right] at h2
  rw [h2, mul_assoc, hf.1 γ γ.2]

end GlobalTheory.ExpCover


open GlobalTheory.ExpCover in
set_option maxHeartbeats 600000 in
theorem _root_.GlobalTheory.T.maximalIdeals_meeting_subspace_cover : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G0 : Type) [Group G0] [Fintype G0] (Pl0 : Type) (B : BlockDat K G0 Pl0) (w : HeightOneSpectrum (𝓞 K)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) [hm : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] [@IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam)) _ hm.toSMul _], F.Ok → F.IsJ lam jK → F.IsHecke lam jK (NablaT F.O N lam) → ∀ (R : Reads F lam B w) (ℓ : Lvl K G0) (Z : Submodule K B.S.Forms), (∀ i, Z ≤ Z.comap (B.op i)) → Covers B ℓ Z w fun m : {m : MaximalSpectrum F.T // ∃ θ, R.Occurs Z θ ∧ F.Over θ m.asIdeal} => haveI := m.1.isMaximal.isPrime; F.setting lam jK m.1.asIdeal := by
  intro K _ _ _ G0 _ _ Pl0 B w _ ι _ _ N F lam jK hm hst hOk hJ hH R ℓ Z hZ J hInc z hz
  have hfZ : B.toF ℓ Z z ∈ Z := toF_mem B ℓ Z z
  have hfN := (mem_cutZ B ℓ Z z).1 hz
  apply final_step
  apply R.del
  obtain ⟨hbinj, hbli, -⟩ := GlobalTheory.LatBC.bc_props F.emb N lam hOk.ring.1
  have hnorm := emb_norm _ ι N F hOk
  obtain ⟨x, hx⟩ := form_lift _ ι N F lam jK (GlobalTheory.LatBC.bc F.emb N lam) hbinj (GlobalTheory.LatBC.bc_grp F.emb N lam) hJ
    (R.rd (B.toF ℓ Z z)) (R.form _) (fun g => (GlobalTheory.LatBC.latN_iff F lam _).1 (R.nab _ hfN g))
  have hfin := forms_fin _ ι N F lam jK hOk
  have hfinV : Module.Finite F.O (NablaT F.O N lam) := GlobalTheory.NablaFin.nablaT_finite F.O N ι lam
  have hxS : (fun g => GlobalTheory.LatBC.bc F.emb N lam ((x : F.G → NablaT F.O N lam) g)) ∈
      Submodule.span (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (R.rd '' Z) := by
    have e : (fun g => GlobalTheory.LatBC.bc F.emb N lam ((x : F.G → NablaT F.O N lam) g)) = R.rd (B.toF ℓ Z z) := funext hx
    rw [e]
    exact Submodule.subset_span (Set.mem_image_of_mem _ hfZ)
  have hloc : ∀ (m : Ideal (MvPolynomial F.I F.O)) (hmax : m.IsMaximal) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ i, ‖θ i‖ ≤ 1) →
      (∀ p, p ∈ m ↔ ‖MvPolynomial.eval₂ F.emb θ p‖ < 1) →
      (∃ v ∈ Submodule.span (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (R.rd '' Z), v ≠ 0 ∧
        ∀ i g, F.emb (F.cst i) • ∑ s ∈ F.tr i, v (g * s) = θ i • v g) →
      (haveI := hmax.isPrime; F.setting lam jK m).Incl (Formalism.EigenvalueLevelCeiling.plc w) J := by
    rintro m hmax θ h1 h2 ⟨v, hvS, hv0, hv⟩
    have h5 := hInc ⟨⟨m, hmax⟩, θ,
      ⟨v, hvS, hv0, isForm_of_span F lam _ (by rintro _ ⟨f, -, rfl⟩; exact R.form f) v hvS, hv⟩, h1, h2⟩
    exact h5
  have k1 := @values_mem_of_local (Formalism.EigenvalueLevelCeiling.plc w) _ F.O F.I F.G (NablaT F.O N lam) (NablaT (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) N lam)
    _ _ _ _ _ _ hfinV _ _ (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))
  have k1b := @k1 hm
  have k2 := @k1b hst hfin F.emb hOk.ring.1 hnorm.1 hnorm.2 (GlobalTheory.LatBC.bc F.emb N lam) hbinj hbli F.tr F.cst
  have k3 := k2 hH.2
  have k3b := k3 (tensSub (deltaIn F.O N lam)) (Submodule.span _ (R.rd '' Z)) (span_stable R Z hZ) x hxS ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : F.O) J
  have k4 := k3b {y | ∀ g, (y : F.G → NablaT F.O N lam) g ∈ tensSub (deltaIn F.O N lam)} (fun _ hy => hy)
  clear k1 k1b k2 k3 k3b
  have k5 := k4 (fun m hmax θ h1 h2 h3 y => by
    have h7 := hloc m hmax θ h1 h2 h3
    unfold HidaSetting.Incl TopIncl locSet at h7
    obtain ⟨x', hx', s, hs⟩ := h7 y
    exact ⟨x', fun g => (Submodule.mem_pi.1 (Submodule.mem_inf.1 hx').2) g (Set.mem_univ _), s, hs⟩)
  have key : ∀ g, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : F.O) ^ J • (x : F.G → NablaT F.O N lam) g ∈ tensSub (deltaIn F.O N lam) := by
    intro g
    have h7 := k5 g
    rw [Submodule.coe_smul, Pi.smul_apply] at h7
    exact h7
  intro g
  apply latD_of F lam
  refine ⟨_, key g, ?_⟩
  rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hx, Pi.smul_apply]
  simp only [map_pow, map_natCast]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PageEstimateStatement
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

namespace GlobalTheory.BigOn.PageNumbers

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L}

theorem le_sup_fin (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (k : ℕ) (hk : k < D.R.m) :
    WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK (k + 1)) ≤
      Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK ((j : ℕ) + 1)) := by
  have h := Finset.le_sup (f := fun j : Fin D.R.m => WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK ((j : ℕ) + 1)))
    (Finset.mem_univ (⟨k, hk⟩ : Fin D.R.m))
  exact h

theorem sup_fin_eq_topDeg (Tp : ParamsT D L Pm) (hK : DV.KapDef D) :
    (Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK ((j : ℕ) + 1))) = GlobalTheory.IndexAssembly.topDeg Tp hK := by
  apply le_antisymm
  · exact Finset.sup_le fun j _ => GlobalTheory.IndexAssembly.le_topDeg Tp hK ⟨by omega, by omega⟩
  · refine Finset.sup_le fun j hj => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact le_sup_fin Tp hK k (by omega)

end GlobalTheory.BigOn.PageNumbers

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.BigOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimePowerLatticeInclusionOfLocalModels
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory.ExpTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lIncl_of_models : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type) (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] [DecidableEq ι] (P : Par) (W : Wts ι), NumOk P W → (Formalism.EigenvalueLevelCeiling.plc w).Prime → W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∀ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) (I : Type) (X : I → HidaSetting ι P.Nr W.lam), Covers B ℓ Z w X → (∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)) → LIncl B ℓ Z w (W.coarseWeightBound P (Formalism.EigenvalueLevelCeiling.plc w)) := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z w ι _ _ P W hN hl hR fr cj I X hC hX
  obtain ⟨hH, hL, hW, -⟩ := hN
  obtain ⟨hW', hJ⟩ := GlobalTheory.expo_frob_indep P hH hL ι W hW fr cj
  have hEq := hJ _ hl hR
  apply hC
  intro i
  obtain ⟨hu, hLk⟩ := hX i
  have hWI := Formalism.CohomologicalDescent.ShortWeightBounds.weight_inputs_of_linkage_holds P hH hL ι (reFr W fr cj) hW' _ (X i) hl hR.1 hLk
  have h := (Formalism.CohomologicalDescent.Top.inclusion_w_seven_real_holds P hH hL ι (reFr W fr cj) hW' _ (X i) hl hu hR.1 hWI).1
  unfold reFr at h
  rw [hEq] at h
  exact h

end GlobalTheory.ExpTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_line_polynomial_equivariance : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → (∀ γ ∈ Lines σ G.V, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')), ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ G.M.Pol B.ψ B.emb) ∧ (∀ k ∈ KInf σ G.V B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ G.M.Pol B.ψ B.emb) ∧ (∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin a × Fin (a + a')), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁) ∧ (∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb, Acts (evI F) (om (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, k)) f f₂ → f₂ = f₁) := by
  first | exact @GlobalTheory.PolStabInf.polStab | exact GlobalTheory.PolStabInf.polStab | (intros; apply GlobalTheory.PolStabInf.polStab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunNumericalConditionsHoldAlongFamily
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.OntoNum

theorem pageNum_along : ∀ x₁ : ℝ, Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x,
    PageNum (Fm.parT x hx ι) x₁ ∧ 3 ≤ (Fm.L x ι).sc.x ∧ ((Fm.D x ι).R.k : ℝ) * (Fm.L x ι).sc.b' ≤ (Fm.L x ι).sc.b ∧
      3 ≤ (Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 5) ∧ 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 4 ≤ (Fm.D x ι).R.nV := by
  intro x₁
  obtain ⟨ε1, hε1, hS⟩ := _root_.GlobalTheory.OntoSizeRows.sizeRows_along
  refine ⟨ε1, hε1, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := hS eps he hle
  refine ⟨K.sup ⟨1000, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hc hL => ?_⟩
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup _ _ CH).1 hL
  have hCP : (1000 : ℝ) ≤ Fm.CP := hL2.1 Fm.CP (by simp [FamP.cPre])
  obtain ⟨xa, hxa⟩ := hK Fm CH hc hL1
  obtain ⟨xb, hxb⟩ := GlobalTheory.FinalRows.rows_of_pageFix eps Fm hc.1 hCP
  refine ⟨max (max xa xb) x₁, fun x hx hx0 ι => ?_⟩
  have hs := hxa x hx (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0) ι
  obtain ⟨hSz, hCnW, hg, hCP', hz, -, -, hsx, -⟩ := hxb x hx (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0) ι
  have hx1 : x₁ ≤ (Fm.L x ι).sc.x := by rw [hsx]; exact le_trans (le_max_right _ _) hx0
  exact ⟨⟨hSz, hCnW, hg, hCP', hz, hx1⟩, GlobalTheory.IndexAssembly.three_le_scale_of_pow_bound hs.2.1, hs.2.2.2.2.2.2.2.2.1, by linarith [hs.2.1],
    (Fm.parT x hx ι).nV_ge⟩

end GlobalTheory.OntoNum

end
end

