module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0340
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoprimeProjectionAdelicLatticeIntoColumns
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviConjHaarModulus
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelHeightBoundSection
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivariantUnitaryCoefficientMapOnto
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem coefficient_map_exists_onto : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∃ J : X.Vpi u →ₗ⋆[ℂ] (Formalism.L2.Forms.Fr D 0 (Nat.zero_le _) → ℂ), JOK X u F wt J ∧ ∀ p ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0), ∃ ξ, J ξ = p := by
  intro D X u F wt hw
  obtain ⟨o, ho, hfr⟩ := _root_.GlobalTheory.St.CFrame.frame_of_type D X u wt hw
  let e := Equiv.piCongrLeft (X.Vloc u) X.pl.symm
  have he : ∀ (x : ∀ τ, X.Vloc u (X.pl.symm τ)) τ, e x (X.pl.symm τ) = x τ := fun x τ =>
    Equiv.piCongrLeft_apply_apply (X.Vloc u) X.pl.symm x τ
  let tens : (∀ τ, X.Vloc u (X.pl.symm τ)) → X.Vpi u := fun x => X.tensU u (e x)
  have hin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ τ, ⟪x τ, y τ⟫_ℂ := by
    intro x y
    show ⟪X.tensU u (e x), X.tensU u (e y)⟫_ℂ = _
    rw [X.tensU_inner, ← Equiv.prod_comp X.pl.symm]
    exact Finset.prod_congr rfl fun τ _ => by rw [he, he]
  have hsp : Submodule.span ℂ (Set.range tens) = ⊤ := by
    have : Set.range tens = Set.range (X.tensU u) := e.surjective.range_comp _
    rw [this]; exact X.tensU_span u
  have hty : ∀ τ, IsHCTypeU D.R.k (fun i => (((D.hcW u τ).u i : ℚ) : ℝ)) (X.piLoc u (X.pl.symm τ)) := by
    intro τ
    have h := X.piLoc_type u (X.pl.symm τ)
    rwa [X.pl.apply_symm_apply] at h
  obtain ⟨Jp, hJv, hJs, hJi, hJe⟩ := _root_.GlobalTheory.TenTypes.tensor_dict D.what₂.Tau D.R.k (D.R.N 0) D.R.N_zero.symm
    (Formalism.L2.Forms.lamT u 0) (fun τ i => (((D.hcW u τ).u i : ℚ) : ℝ))
    (fun τ i => GlobalTheory.hcParam_eq_weight_step_zero_add_rho D u τ i)
    (fun τ => X.Vloc u (X.pl.symm τ)) (fun τ => X.piLoc u (X.pl.symm τ)) hty (X.Vpi u) tens hin hsp
  have hoinv : ∀ τ, IsUnit ((o.1 τ)⁻¹).det := fun τ => by
    have h := o.2 τ
    rw [Matrix.det_nonsing_inv]
    exact (Ring.inverse_unit h.unit ▸ (h.unit⁻¹).isUnit)
  have hmap := GlobalTheory.ValueSpaceCoordinates.map_fnOf_eq_ValC D.what₂.Tau (D.R.N 0) (Formalism.L2.Forms.lamT u 0)
    (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D))
    (fun τ => (o.1 τ)⁻¹) hoinv
  let fo := Formalism.L2.Forms.fnOf (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D))
    (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u 0)) (fun τ => (o.1 τ)⁻¹)
  refine ⟨fo.comp Jp, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro s hs ξ y y' hyy
    obtain ⟨m, hm⟩ := hfr s hs
    have hA : ∀ x, X.piU u s (tens x) = tens (fun τ =>
        X.piLoc u (X.pl.symm τ) ((m τ).submatrix (Fin.cast D.R.N_zero.symm) (Fin.cast D.R.N_zero.symm)) (x τ)) := by
      intro x
      show X.piU u s (X.tensU u (e x)) = X.tensU u (e _)
      rw [X.tensU_equiv u s hs (e x)]
      congr 1
      funext v
      obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
      rw [he, he, (hm τ).2.1]
    have hy : Formalism.L2.Forms.IsTr (fun τ => o.1 τ * m τ * (o.1 τ)⁻¹) y' y := fun τ => by
      rw [hyy τ, (hm τ).2.2]
    exact hJe m (fun τ => (hm τ).1) (X.piU u s) hA _ o.1 (fun τ => o.2 τ) ξ y y' hy
  · intro ξ
    rw [← hmap]
    exact ⟨Jp ξ, hJv ξ, rfl⟩
  · intro c ξ η
    have hon : o.IsON := fun τ => Or.inl (ho τ)
    have hP : ∀ ζ, Jp ζ ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam 0) := fun ζ => by
      rw [← Formalism.L2.Forms.lamT_zero]; exact hJv ζ
    have h := F.val0.ipV c o hon (Jp ξ) (hP ξ) (Jp η) (hP η)
    rw [← Formalism.L2.Forms.lamT_zero] at h
    exact h.trans (hJi ξ η)
  · intro p hp
    rw [← hmap] at hp
    obtain ⟨P, hP, rfl⟩ := hp
    obtain ⟨ξ, rfl⟩ := hJs P hP
    exact ⟨ξ, rfl⟩

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameAdelicColumnLatticeLinkedReference
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.FrameLink

theorem frame_exists : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∃ Fr : FrQ D wt, FrLink X u wt ιA Fr := by
  intro D X u wt ιA hW hI
  obtain ⟨c, p, hc, hrng, hid, hLf, hkill, hkz, hcl⟩ := _root_.GlobalTheory.St.G.g_proj D X u wt ιA hW hI
  have hmhat := _root_.GlobalTheory.St.G.MHat.mhat_coords D X u wt ιA hW hI
  have hY : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ X.B.I.Lf ∧ X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ X.B.I.Lf := fun i =>
    ⟨(X.xu_K u (X.bw i)).1 (X.vectorsInLattice.2.2 i).1, (X.xu_K u (X.bwd i)).1 (X.vectorsInLattice.2.2 i).2⟩
  have hb0 : ∀ i, ∃ x, embA X wt ιA x = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) := fun i => by
    obtain ⟨x, hx⟩ := hrng ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u) *ᵥ X.bw i))
    exact ⟨x, by rw [← hx, map_smul]⟩
  have hbd0 : ∀ i, ∃ x, embA X wt ιA x = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) := fun i => by
    obtain ⟨x, hx⟩ := hrng ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))
    exact ⟨x, by rw [← hx, map_smul]⟩
  choose b hb using hb0
  choose bd hbd using hbd0
  have hclose := _root_.GlobalTheory.St.G.FrameClose.typeVec_close D X u wt ιA hW hI c p hcl
  have hbe := _root_.GlobalTheory.St.G.FrameEps.beps D X u wt ιA hW hI c p b bd hb hbd
  refine ⟨{ eps := ιA X.ew
            eps_idem := by rw [← map_mul, X.ew_idem]
            eps_orth := by rw [← GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hI, ← map_mul, X.ew_orth, map_zero]
            eps_int := (hI.2 _).1 X.ew_int
            eps_full := _root_.GlobalTheory.St.G.FrameFull.eps_full D X u wt ιA hW hI
            b := b
            bd := bd
            b_mem := fun i => (hmhat.1 (b i)).2 (by rw [hb i]; exact hLf _ (hY i).1)
            bd_mem := fun i => (hmhat.1 (bd i)).2 (by rw [hbd i]; exact hLf _ (hY i).2)
            b_eps := hbe.1
            bd_eps := hbe.2
            dual := _root_.GlobalTheory.St.G.DualMod.dual_mod D X u wt ιA hW hI c p b bd hb hbd hclose
            span := _root_.GlobalTheory.St.G.FrameSpan.span_mod D X u wt ιA hW hI c p hc hid hLf hkill hkz b bd hb hbd
            psi := fun a => X.psiEf (ιA.symm a)
            psi_add := fun x y => by
              show X.psiEf (ιA.symm (x + y)) = X.psiEf (ιA.symm x) * X.psiEf (ιA.symm y)
              rw [RingEquiv.map_add (e := _), X.psiEf_add]
            psi_int := fun x hx => X.psiEf_int _ ((hI.2 _).2 (by simpa using hx))
            psi_rat := GlobalTheory.T.transportedFiniteCharacter_inverse_exp_trace D X ιA hI }, rfl, fun i => ?_, fun i => ?_, fun a => rfl⟩
  · show embA X wt ιA (b i) - _ ∈ _
    rw [hb i]; exact (hclose i).1
  · show embA X wt ιA (bd i) - _ ∈ _
    rw [hbd i]; exact (hclose i).2

end GlobalTheory.St.G.FrameLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLatticeRepresentativeNormalised
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowPartner

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem mem_orth_iff (U : Submodule E S.V) (y : S.V) : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem X_iso (F : LFlag S r T) {x y : S.V} (hx : x ∈ Xsp F) (hy : y ∈ Xsp F) : S.hT x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨b, rfl⟩ := hy; exact F.fl.e_iso a b
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul c u _ hu => simp [hu]

theorem z_mem_orth (F : LFlag S r T) : F.fl.z ∈ orth S (Xsp F) := by
  rw [mem_orth_iff]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact F.fl.z_orth a
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul c u _ hu => simp [hu]

theorem X_le_orth (F : LFlag S r T) : Xsp F ≤ orth S (Xsp F) := fun y hy =>
  (mem_orth_iff _ _).2 fun x hx => X_iso F hx hy

theorem half_not_int : ¬ ∃ o : 𝓞 E, (o : E) = algebraMap ℚ E (1 / 2) := by
  rintro ⟨o, ho⟩
  have h1 : IsIntegral ℤ (algebraMap ℚ E (1 / 2)) := by rw [← ho]; exact o.2
  rw [isIntegral_algebraMap_iff ] at h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  have h2 : ((2 * n : ℤ) : ℚ) = 1 := by push_cast; rw [show (algebraMap ℤ ℚ n) = (n : ℚ) from rfl] at hn; rw [hn]; norm_num
  have h3 : 2 * n = 1 := by exact_mod_cast h2
  omega

end Gen

end GlobalTheory.RowPartner

namespace GlobalTheory.RowPartner

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem span_eq_top_of_unimodular (L : Submodule (𝓞 E) S.V)
    (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT L) :
    Submodule.span E (L : Set S.V) = ⊤ := by
  by_contra hspan
  obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨μ, hμ⟩ := GlobalTheory.LoopC.FunIdx.exists_vec S φ
  have hμ₀ : μ ≠ 0 := by
    intro h
    apply hφ₀
    ext y
    simpa [h] using hμ y
  have hline (a : E) : a • μ ∈ L := by
    rw [← hU]
    change a • μ ∈ Formalism.E.hdual S.hT L
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply]
    intro y hy
    have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
    simp [← S.herm.eq (a • μ) y, LinearMap.map_smulₛₗ, ← hμ, hy₀]
  obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
    (show μ ∉ (⊥ : Submodule E S.V) by simpa using hμ₀)
  let f := ψ.restrictScalars (𝓞 E)
  have hmap (x : E) : x ∈ L.map f := by
    refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
    change ψ ((x / ψ μ) • μ) = x
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
  obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
    (S := nonZeroDivisors (𝓞 E)) (hL.fg.map f)
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hne {a : 𝓞 E} (ha : a ≠ 0) : algebraMap (𝓞 E) E a ≠ 0 :=
    fun h => ha (hinj (h.trans (map_zero _).symm))
  have hinteger (x : E) : IsLocalization.IsInteger (𝓞 E) x := by
    have hx := hd _ (hmap ((algebraMap (𝓞 E) E d)⁻¹ * x))
    rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
      one_mul] at hx
  apply RingOfIntegers.not_isField E
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 E) E a)⁻¹)
  refine ⟨b, hinj ?_⟩
  rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]

theorem exists_smul_mem_lat (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT L) (x : S.V) :
    ∃ r : 𝓞 E, r ≠ 0 ∧ r • x ∈ L := by
  have hfull : Submodule.IsFullLattice E L :=
    { toIsLattice := hL, span_eq_top := span_eq_top_of_unimodular L hL hU }
  exact GlobalTheory.NonzeroIntegerSmulMem.exists_ne_zero_smul_mem L hfull x

theorem z_not_mem_X (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T)
    (hprim : ∀ c : E, c • F.fl.z ∈ Lsub Λ F → ∃ o : 𝓞 E, (o : E) = c) : F.fl.z ∉ Xsp F := by
  intro hz
  apply half_not_int (E := E)
  apply hprim
  have hc : algebraMap ℚ E (1 / 2) • F.fl.z ∈ Xsp F := (Xsp F).smul_mem _ hz
  exact ⟨Submodule.mem_sup_right hc, X_le_orth F hc⟩

theorem exists_partner_rep (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T)
    (hlat : Submodule.IsLattice E Λ) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hz : F.fl.z ∈ Λ)
    (hprim : ∀ c : E, c • F.fl.z ∈ Lsub Λ F → ∃ o : 𝓞 E, (o : E) = c) :
    ∃ σ ∈ Lrep Λ F, S.hT σ F.fl.z = 1 := by
  have hzX := z_not_mem_X Λ F hprim
  obtain ⟨φ, hφX, hφz⟩ := LinearMap.exists_extend_of_notMem (0 : Xsp F →ₗ[E] E) hzX 1
  have hφ0 : ∀ y ∈ Xsp F, φ y = 0 := fun y hy => by simpa using congr($hφX ⟨y, hy⟩)
  set U : Submodule E S.V := Xsp F ⊔ Submodule.span E {F.fl.z} with hUdef
  set M0 : Submodule (𝓞 E) S.V := Λ ⊓ toO S U with hM0
  have hUo : U ≤ orth S (Xsp F) := sup_le (X_le_orth F)
    ((Submodule.span_singleton_le_iff_mem _ _).2 (z_mem_orth F))
  have hprimM : IsPrimitiveSub M0 Λ := by
    refine ⟨inf_le_left, le_antisymm (le_inf inf_le_left fun x hx => Submodule.subset_span hx) ?_⟩
    refine inf_le_inf_left _ ?_
    intro x hx
    exact (Submodule.span_le (p := U)).2 (fun y (hy : y ∈ M0) => hy.2) hx
  have hint : ∀ x : M0, ∃ o : 𝓞 E, (o : E) = φ x := by
    rintro ⟨x, hxΛ, hxU⟩
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 (show x ∈ U from hxU)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have hxo : y + a • F.fl.z ∈ orth S (Xsp F) := hUo hxU
    obtain ⟨o, ho⟩ := hprim a ⟨by
        have h1 : y + a • F.fl.z ∈ Lrep Λ F := ⟨hxΛ, hxo⟩
        have h2 : -y ∈ toO S (Xsp F) := (Xsp F).neg_mem hy
        have := Submodule.add_mem_sup h1 h2
        simpa using this, (orth S (Xsp F)).smul_mem a (z_mem_orth F)⟩
    refine ⟨o, ?_⟩
    simp [map_add (f := _), hφ0 y hy, hφz, ho]
  choose ψ hψ using hint
  let ψ' : M0 →ₗ[𝓞 E] 𝓞 E :=
    { toFun := ψ
      map_add' := fun x y => by
        apply RingOfIntegers.ext
        simp [hψ]
      map_smul' := fun c x => by
        apply RingOfIntegers.ext
        simp only [hψ, RingHom.id_apply, smul_eq_mul, map_mul, Submodule.coe_smul]
        rw [← algebraMap_smul E c (x : S.V), map_smul]
        simp [hψ] }
  have hfull : Submodule.IsFullLattice E Λ :=
    { toIsLattice := hlat, span_eq_top := span_eq_top_of_unimodular Λ hlat hU }
  obtain ⟨w, hw⟩ := GlobalTheory.LoopC.FunIdx.exists_dual_vec S M0 Λ hfull hprimM ψ'
  have hwM : ∀ x (hx : x ∈ M0), S.hT w x = φ x := fun x hx => by
    rw [← hw ⟨x, hx⟩]; exact hψ ⟨x, hx⟩
  have hwΛ : (w : S.V) ∈ Λ := by
    have := w.2.1
    rwa [hU] at this
  refine ⟨w, ⟨hwΛ, ?_⟩, ?_⟩
  · show (w : S.V) ∈ orth S (Xsp F)
    rw [mem_orth_iff]
    intro x hx
    obtain ⟨c, hc0, hcx⟩ := exists_smul_mem_lat Λ hlat hU x
    have hcX : c • x ∈ Xsp F := by
      rw [← algebraMap_smul E c x]; exact (Xsp F).smul_mem _ hx
    have hm : c • x ∈ M0 := ⟨hcx, Submodule.mem_sup_left hcX⟩
    have h1 := hwM _ hm
    rw [hφ0 _ hcX] at h1
    have h2 : S.hT w x = 0 := by
      rw [← algebraMap_smul E c x, map_smul, smul_eq_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left (by simpa using hc0)
    rw [← S.herm.eq, h2]; simp
  · rw [hwM _ ⟨hz, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)⟩, hφz]

end Gen

end GlobalTheory.RowPartner

namespace GlobalTheory.RowPartner

theorem exists_partner_rowLat : ∀ (D : D7) (T : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D),
    IsRowLat D F0 Λ → ∃ σ ∈ Lrep Λ (lf D F0), (VS D).hT σ F0.z = 1 := by
  intro D T F0 Λ h
  obtain ⟨_, ⟨hlat, hU, ⟨hz, _⟩, ⟨_, hprim⟩⟩, _⟩ := h
  exact exists_partner_rep Λ (lf D F0) hlat hU hz hprim

end GlobalTheory.RowPartner
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtDerivedActionMaxCompactAverage
section
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

theorem hasDerivAt_exp_integral_dsigW (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ) (v : H)
    (D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hσ' : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hμ : GlobalTheory.KFinAvg.IsHaarKH k r μ)
    (hφ : Continuous φ) (hv : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v)
    (hD : ∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) (hX : Formalism.MainNotions.S.InLieHpk k r X) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X))
        (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ))
      (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v) ∂μ) 0 := by
  have hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) σ := hσ'
  obtain ⟨hprob, hK0, -, -⟩ := hμ
  have hKc := isCompact_KH k r
  have hae : ∀ᵐ g ∂μ, g ∈ GlobalTheory.ThA.KH k r := mem_ae_iff.2 hK0
  have hres : μ.restrict (GlobalTheory.ThA.KH k r) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have hint : ∀ D' : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      (∀ Y ∈ D', Formalism.MainNotions.S.InLieHpk k r Y) →
      Integrable (fun g => φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D' (σ g v)) μ := by
    intro D' hD'
    have h1 : ContinuousOn (fun g => φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D' (σ g v)) (GlobalTheory.ThA.KH k r) :=
      hφ.continuousOn.smul ((Formalism.MainNotions.LowestKTypeMultiplicity.orbit_cont hσ hv D' hD').mono Set.inter_subset_left)
    have h2 : IntegrableOn (fun g => φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D' (σ g v)) (GlobalTheory.ThA.KH k r) μ :=
      h1.integrableOn_compact hKc
    rwa [IntegrableOn, hres] at h2
  have hXD : ∀ Y ∈ X :: D, Formalism.MainNotions.S.InLieHpk k r Y := by
    intro Y hY
    rcases List.mem_cons.1 hY with h | h
    · rw [h]; exact hX
    · exact hD Y h
  have hexp := Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hX
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ) (x₀ := (0 : ℝ))
    (F := fun (t : ℝ) g => σ (NormedSpace.exp ((t : ℂ) • X))
      (φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v)))
    (F' := fun (t : ℝ) g => σ (NormedSpace.exp ((t : ℂ) • X))
      (φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v)))
    (bound := fun g => ‖φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v)‖) (s := Set.univ)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      ((σ (NormedSpace.exp ((t : ℂ) • X))).integrable_comp (hint D hD)).aestronglyMeasurable)
    ((σ _).integrable_comp (hint D hD))
    ((σ _).integrable_comp (hint _ hXD)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g t _ => (hσ.2.1 _ (hexp t) _).le)
    (hint _ hXD).norm
    (by
      filter_upwards [hae] with g hg t _
      have hsm := Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv hg.1
      have h0 := (Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hsm D hD hX).const_smul (φ g)
      have h1 := ((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
      rw [← sub_self t] at h1
      have h2 := h1.comp_sub_const t t
      simp only [map_smul]
      convert (preTransparency := .reducible) h2 using 1
      · funext s
        have e : NormedSpace.exp ((s : ℂ) • X) =
            NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((s - t : ℝ) : ℂ) • X) := by
          rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _), ← add_smul]
          congr 2
          push_cast; ring
        rw [e, hσ.1.2 _ (hexp t) _ (hexp (s - t))]
        simp only [Function.comp, Pi.smul_apply, ContinuousLinearMap.coe_restrictScalars', map_smul]
        rfl
      · simp)
  have h3 := key.2
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, one_apply_eq_self] at h3
  convert h3 using 1
  funext t
  exact ((σ _).integral_comp_comm (hint D hD)).symm

end GlobalTheory.KFinAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviConjHaarModulusStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlag_levi_conj_haar_modulus : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, 1 ≤ j i) → IsIsoFlag ε j W → ∀ μ, IsGaugeSub (flagN ε W) (dimN n j) μ → ∀ m ∈ flagM ε W, μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) • μ := by
  first | exact @GlobalTheory.FlagModulus.modulus | exact GlobalTheory.FlagModulus.modulus | (intros; apply GlobalTheory.FlagModulus.modulus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelHeightBoundSectionStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_height_bound_section : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → ∀ De R₀ : ℝ, DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (q : PSec k r j × (UToff β → ℂ)) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg2 k r z' (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → Sg k r z (g₀ * (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m))) ≤ R₀ → (∀ p, ‖q.2 p‖ ≤ R₀ ^ (2 * r) * De) ∧ (∀ b, eucl (m⁻¹ *ᵥ q.1.1 b) ≤ R₀ ^ (2 * r) * De) ∧ (∀ p, ‖q.1.2.1 p‖ ≤ 2 * r * (R₀ ^ (2 * r) * De) ^ 2) ∧ ∀ b, |q.1.2.2 b| ≤ 2 * r * (R₀ ^ (2 * r) * De) ^ 2 := by
  first | exact @GlobalTheory.Amp.SecBound.section_coord_le | exact GlobalTheory.Amp.SecBound.section_coord_le | (intros; apply GlobalTheory.Amp.SecBound.section_coord_le <;> assumption)
end

