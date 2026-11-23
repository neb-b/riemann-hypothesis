module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0328
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0384
public import Formalism.AdmissibleDesigns.Bundle0001
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointParameterIsTypeParameterOfTame
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.ParOfPoint

theorem inePol_foldr (D : D7) {w : PlE D.host} (x : D.naut.LP w) {α : Type} (c : α → ℝ) (l : List α)
    (σ : GE D.nd) (hσ : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (l.foldr (fun k acc => D.naut.lpSum (D.naut.lpTw x (c k)) acc) (D.naut.lpZero w)) σ =
      D.naut.inePol x σ ^ l.length := by
  induction l with
  | nil =>
    have h := ((D.naut.unr_iff_ine (D.naut.lpZero w)).1 (D.naut.lpZero_unr w)).2 σ hσ
    rw [D.naut.lpDim_zero, pow_zero] at h
    simpa using h
  | cons k l ih =>
    simp only [List.foldr_cons, List.length_cons]
    rw [D.naut.inePol_sum, D.naut.inePol_tw _ _ σ hσ, ih, pow_succ, mul_comm]

theorem inePol_twistIso (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut) (L : List (Part D.naut.CG)) (w : PlE D.host)
    (σ : GE D.nd) (hσ : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaTinv) w) σ =
      D.naut.inePol (isoLoc D.nd D.naut L w) σ := by
  have hd : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ w
  have hu : D.naut.inePol (D.naut.locG D.naut.etaTinv w) σ = X - C 1 := by
    have h := ((D.naut.unr_iff_ine _).1 (D.naut.etaTinv_def w).1).2 σ hσ
    rw [hd, pow_one] at h
    rw [h, map_one]
  have hpart : ∀ {a : ℕ} (π : D.naut.CG a),
      D.naut.inePol (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) σ = D.naut.inePol (D.naut.locG π w) σ := by
    intro a π
    rw [D.naut.locG_tw, ((hT w (D.naut.locG π w) (D.naut.locG π w) _ _ 0 hd hd).2.2.2.2.2 σ hσ).2 1 hu,
      Polynomial.scaleRoots_one]
  induction L with
  | nil => rfl
  | cons p L ih =>
    show D.naut.inePol (D.naut.lpSum (spehLoc D.nd D.naut ⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ w)
      (isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaTinv) w)) σ =
      D.naut.inePol (D.naut.lpSum (spehLoc D.nd D.naut p w) (isoLoc D.nd D.naut L w)) σ
    rw [D.naut.inePol_sum, D.naut.inePol_sum, ih]
    unfold spehLoc
    rw [inePol_foldr D _ _ _ σ hσ, inePol_foldr D _ _ _ σ hσ, hpart]

theorem eq_pow_of_mul_eq (A B : ℂ[X]) (n : ℕ) (hA : A.Monic) (hB : B.Monic) (h : A * B = (X - 1) ^ n) :
    A = (X - 1) ^ A.natDegree := by
  have hdvd : A ∣ (X - C 1) ^ n := by rw [map_one, ← h]; exact dvd_mul_right A B
  obtain ⟨j, -, hj⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C (1 : ℂ)) n).1 hdvd
  have e := Polynomial.eq_of_monic_of_associated hA ((monic_X_sub_C (1 : ℂ)).pow j) hj
  rw [e, (monic_X_sub_C (1 : ℂ)).natDegree_pow, natDegree_X_sub_C, mul_one, map_one]

theorem tw_back (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut)
    (hAN : ∀ Pa Pa' : List (Part D.naut.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w) → Pa.Perm Pa')
    {a : ℕ} (ha : 1 ≤ a) (π : D.naut.CG a) : D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT = π := by
  have hsing : ∀ (π' : D.naut.CG a) w, isoLoc D.nd D.naut [⟨a, π', 1⟩] w = D.naut.locG π' w := by
    intro π' w
    show D.naut.lpSum (spehLoc D.nd D.naut ⟨a, π', 1⟩ w) (D.naut.lpZero w) = _
    rw [D.naut.lpSum_zero]
    unfold spehLoc
    simp [D.naut.lpSum_zero, D.naut.lpTw_zero]
  have h := hAN [⟨a, D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      rw [hsing, hsing, D.naut.locG_tw, D.naut.locG_tw]
      exact (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hT _).2)
  rw [List.singleton_perm_singleton] at h
  injection h with _ h2

theorem main : ∀ D : D7, (∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → LabDepth D → DepthZ D → ParSurj D := by
  intro D hPar h0 h5 hsplit hLab hDZ i x Sig hX
  obtain ⟨P, -, hB⟩ := hX
  have hT : SumRepresentations.At.TieLP D.nd D.naut := h0.1
  have hAN := h5.1
  set χ := D.naut.etaTinv with hχ
  have htw : twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) χ =
      twistIso D.nd D.naut Sig χ ++ twistIso D.nd D.naut [muPart D.nd D.naut i] χ := List.map_append

  have hparts : ∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π := by
    intro p hp
    have hm : (⟨p.a, D.naut.tw p.π χ, p.d⟩ : Part D.naut.CG) ∈
        twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) χ := by
      rw [htw]
      exact List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩)
    obtain ⟨ha, hd, hc⟩ := hB.1 _ hm
    refine ⟨ha, hd, ?_⟩
    have e := tw_back D hT hAN ha p.π
    rw [← e]
    exact D.naut.csd_tw _ _ h0.2.1.1.1 hc

  have hnodup : (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup := by
    have h2 := hB.2.1
    rw [htw, List.map_append] at h2
    have h3 := (List.nodup_append.1 h2).1
    have e : (twistIso D.nd D.naut Sig χ).map (fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)) =
        (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).map
          (fun q => ((⟨q.1.1, D.naut.tw q.1.2 χ⟩ : Σ a, D.naut.CG a), q.2)) := by
      unfold twistIso
      rw [List.map_map, List.map_map]
      rfl
    rw [e] at h3
    exact h3.of_map _

  have hrank : rankIso D.nd D.naut Sig = D.R.r := by
    have hr := hB.2.2.1
    have e1 : rankIso D.nd D.naut (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) χ) =
        rankIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) := by
      unfold rankIso twistIso
      rw [List.map_map]
      rfl
    rw [e1] at hr
    unfold rankIso at hr ⊢
    rw [List.map_append, List.sum_append] at hr
    simp only [muPart, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at hr
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega

  have hlab : ∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).Monic ∧
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r := by
    intro k v
    set w := D.naut.plGw k v with hw
    have hover := D.naut.plGw_over k v
    obtain ⟨hmon, hiff⟩ := hLab k w hover (isoLoc D.nd D.naut Sig w)
    refine ⟨hmon, ?_⟩
    rw [← hrank, ← lpDim_isoLoc]
    apply hiff.2
    intro σ hσ hwild
    have hloc := hB.2.2.2.1 w (hsplit k v)
    have htame := hDZ i P k w hover σ hσ hwild
    rw [← hloc, inePol_twistIso D hT _ w σ hσ, GlobalTheory.RowThetaParam.isoLoc_append, D.naut.inePol_sum] at htame
    have hd1 : D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 := D.naut.locG_dim _ w
    have hm1 := ((hT w (isoLoc D.nd D.naut Sig w) (isoLoc D.nd D.naut Sig w) _ _ 0 hd1 hd1).2.2.2.2.2 σ hσ).1
    have hm2 := ((hT w (isoLoc D.nd D.naut [muPart D.nd D.naut i] w)
      (isoLoc D.nd D.naut [muPart D.nd D.naut i] w) _ _ 0 hd1 hd1).2.2.2.2.2 σ hσ).1
    have e := eq_pow_of_mul_eq _ _ _ hm1.1 hm2.1 htame
    rw [e, hm1.2]
  exact hPar ⟨Sig, hparts, hnodup, hrank, hlab⟩

end GlobalTheory.ParOfPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimitiveCentralIdempotentEqSimpleRepIdempotent
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.PrimCentIdem

open CategoryTheory

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem eq_sum_single (e : MonoidAlgebra ℂ Γ) : e = ∑ q : Γ, MonoidAlgebra.single q (e.coeff q) := by
  classical
  ext x
  simp [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finsupp.single_apply]

theorem coeff_mul_fin (a b : MonoidAlgebra ℂ Γ) (x : Γ) :
    (a * b).coeff x = ∑ q, a.coeff q * b.coeff (q⁻¹ * x) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  intro q; simp

theorem exists_scalar (e : MonoidAlgebra ℂ Γ) (he : ∀ w, e * w = w * e) (ρ : FDRep ℂ Γ) [Simple ρ] :
    ∃ c : ℂ, ∀ v : ρ, (∑ q : Γ, e.coeff q • ρ.ρ q) v = c • v := by
  let T : ρ →ₗ[ℂ] ρ := ∑ q : Γ, e.coeff q • ρ.ρ q
  have hTA : T = Representation.asAlgebraHom ρ.ρ e := by
    conv_rhs => rw [eq_sum_single e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [T, map_sum, Representation.asAlgebraHom_single]
  have hcomm : ∀ h : Γ, ∀ v : ρ, T (ρ.ρ h v) = ρ.ρ h (T v) := by
    intro h v
    have h1 : Representation.asAlgebraHom ρ.ρ (e * MonoidAlgebra.single h 1) = Representation.asAlgebraHom ρ.ρ (MonoidAlgebra.single h 1 * e) := by
      rw [he]
    rw [map_mul, map_mul, Representation.asAlgebraHom_single, one_smul] at h1
    rw [hTA]
    exact LinearMap.congr_fun h1 v
  let f' : ρ ⟶ ρ := ⟨FGModuleCat.ofHom T, fun g => by
    ext v
    exact hcomm g v⟩
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ f'
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun φ : ρ ⟶ ρ => φ.hom.hom v) hc
  exact this.symm

theorem mul_zIdem_eq_smul (e : MonoidAlgebra ℂ Γ) (ρ : FDRep ℂ Γ) (c : ℂ)
    (hc : ∀ v : ρ, (∑ q : Γ, e.coeff q • ρ.ρ q) v = c • v) :
    e * Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ = c • Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
  ext x
  rw [coeff_mul_fin, MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  simp only [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff]
  have hT : (∑ q : Γ, e.coeff q • ρ.ρ q) = c • (1 : Module.End ℂ ρ) := LinearMap.ext fun v => by simp [hc v]
  have h1 : ∀ q : Γ, ρ.ρ (q⁻¹ * x)⁻¹ = ρ.ρ x⁻¹ * ρ.ρ q := fun q => by rw [mul_inv_rev, inv_inv, map_mul]
  have h2 : ∑ q : Γ, e.coeff q * LinearMap.trace ℂ ρ (ρ.ρ x⁻¹ * ρ.ρ q) =
      LinearMap.trace ℂ ρ (ρ.ρ x⁻¹ * ∑ q : Γ, e.coeff q • ρ.ρ q) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  have h3 : ∑ q : Γ, e.coeff q * ((Module.finrank ℂ ρ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ ρ (ρ.ρ (q⁻¹ * x)⁻¹)) =
      (Module.finrank ℂ ρ : ℂ) / Fintype.card Γ * ∑ q : Γ, e.coeff q * LinearMap.trace ℂ ρ (ρ.ρ x⁻¹ * ρ.ρ q) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [h1]; ring
  rw [h3, h2, hT, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
  ring

end GlobalTheory.PrimCentIdem

open GlobalTheory.PrimCentIdem in
theorem GlobalTheory.PrimCentIdem.main : ∀ (g a : ℕ) [Fact g.Prime] (L : PairedCharacterCondition.LzData g) (τ : L.Irr a),
    ∃ ρ : FDRep ℂ (GL (Fin a) (ZMod g)), CategoryTheory.Simple ρ ∧ L.idem τ = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
  intro g a _ L τ
  classical
  obtain ⟨hfin, hsum⟩ := GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one (GL (Fin a) (ZMod g))
  have hex : ∃ ρ : FDRep ℂ (GL (Fin a) (ZMod g)), CategoryTheory.Simple ρ ∧
      L.idem τ * Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply L.idem_ne τ
    rw [← mul_one (L.idem τ), ← hsum, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
    refine Finset.sum_eq_zero fun z hz => ?_
    obtain ⟨ρ, hρ, rfl⟩ := (Set.Finite.mem_toFinset hfin).1 hz
    exact hno ρ hρ
  obtain ⟨ρ, hρ, hne⟩ := hex
  haveI := hρ
  refine ⟨ρ, hρ, ?_⟩
  set e := L.idem τ with he_def
  set z := Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ with hz_def
  have hzz : z * z = z := (GlobalTheory.SerOSys.zIdem_centralIdempotent ρ hρ).1
  have hee : e * e = e := L.idem_idem τ
  have hec : ∀ w, e * w = w * e := L.idem_central τ
  have hzc : ∀ w, z * w = w * z := (GlobalTheory.SerOSys.zIdem_centralIdempotent ρ hρ).2
  obtain ⟨c, hc⟩ := exists_scalar e hec ρ
  have hmul : e * z = c • z := mul_zIdem_eq_smul e ρ c hc
  have hze : z * e = e * z := hzc e
  have hprim := L.idem_prim τ (e * z)
    (calc e * z * (e * z) = e * (z * e) * z := by simp only [mul_assoc]
      _ = e * (e * z) * z := by rw [hze]
      _ = (e * e) * (z * z) := by simp only [mul_assoc]
      _ = e * z := by rw [hee, hzz])
    (fun w => calc e * z * w = e * (z * w) := mul_assoc _ _ _
      _ = e * (w * z) := by rw [hzc w]
      _ = (e * w) * z := (mul_assoc _ _ _).symm
      _ = (w * e) * z := by rw [hec w]
      _ = w * (e * z) := mul_assoc _ _ _)
    (show e * z * e = e * z from calc e * z * e = e * (z * e) := mul_assoc _ _ _
      _ = e * (e * z) := by rw [hze]
      _ = (e * e) * z := (mul_assoc _ _ _).symm
      _ = e * z := by rw [hee])
  have hez : e * z = e := hprim.resolve_left hne
  have hcz : c • z ≠ 0 := hmul ▸ hne
  have hc0 : c ≠ 0 := fun h => hcz (by rw [h, zero_smul])
  have hz0 : z ≠ 0 := fun h => hcz (by rw [h, smul_zero])
  have hidem : (c * c - c) • z = 0 := by
    have h1 : (c • z) * (c • z) = c • z := by rw [← hmul, hez, hee]
    rw [smul_mul_smul_comm, hzz] at h1
    rw [sub_smul, h1, sub_self]
  have hcc : c * c - c = 0 := (smul_eq_zero.1 hidem).resolve_right hz0
  have hc1 : c = 1 := by
    have : c * (c - 1) = 0 := by rw [mul_sub, mul_one]; exact hcc
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hc0
    · exact sub_eq_zero.1 h
  rw [← hez, hmul, hc1, one_smul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEq
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.Prism.Rigid

theorem φ_mem_of_mem {l : ℕ} (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) {m : Ideal A}
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m) : D.φ x ∈ m := by
  rw [D.φ_eq]
  exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hx _ hl) (Ideal.mul_mem_right _ _ hlm)

theorem φ_mem_sq {l : ℕ} (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) {m : Ideal A}
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m ^ 2) : D.φ x ∈ m ^ 2 := by
  have h : (m ^ 2).map D.φ ≤ m ^ 2 := by
    rw [Ideal.map_pow, sq, sq]
    have hm : m.map D.φ ≤ m := Ideal.map_le_iff_le_comap.2 fun y hy => φ_mem_of_mem hl D hlm hy
    exact Ideal.mul_mono hm hm
  exact h (Ideal.mem_map_of_mem _ hx)

theorem map_I_eq (l : ℕ) [hl : Fact l.Prime] (R : Type) [CommRing R] (B B' : Obj l R) (f : Hom B B') :
    B.I.map f.f = B'.I := by
  have hl0 : 0 < l := hl.out.pos
  have hNI : B.I.map f.f ≤ B'.I := Ideal.map_le_iff_le_comap.2 fun a ha => f.f_I a ha
  refine _root_.GlobalTheory.invertible_ideal_eq_of_not_le_maximal_mul B'.A B'.I (B.I.map f.f) B'.inv hNI ?_
  intro m hm hN

  have hjac : Ideal.span {(l : B'.A)} ⊔ B'.I ≤ m := by
    haveI := B'.complete
    refine le_trans (IsAdicComplete.le_jacobson_bot (Ideal.span {(l : B'.A)} ⊔ B'.I)) ?_
    exact sInf_le ⟨bot_le, hm⟩
  have hlm : (l : B'.A) ∈ m := hjac (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hIm : B'.I ≤ m := le_trans le_sup_right hjac
  have hN2 : B.I.map f.f ≤ m ^ 2 := by
    rw [sq]; exact le_trans hN (Ideal.mul_mono_right hIm)

  have hmap : B.I ⊔ B.I.map B.D.φ ≤ (m ^ 2).comap f.f := by
    refine sup_le (fun a ha => hN2 (Ideal.mem_map_of_mem _ ha)) ?_
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    show f.f (B.D.φ a) ∈ m ^ 2
    rw [f.f_φ]
    exact φ_mem_sq hl0 B'.D hlm (hN2 (Ideal.mem_map_of_mem _ ha))
  have hl2 : (l : B'.A) ∈ m ^ 2 := by
    have := hmap B.l_mem
    simpa [map_natCast] using this
  exact (_root_.GlobalTheory.BSP.LSq.l_not_mem_sq l B'.A B'.D m hm.ne_top hlm).1 hl2

end GlobalTheory.Prism.Rigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismLocalizationSpanNonZeroDivisorBoundedTorsioStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismLocalization_span_nonZeroDivisor_bounded_torsion : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (f d : B.A), GenAway B f d → ∀ M : Submonoid B.A, f ∈ M → B.I.map (algebraMap B.A (Localization M)) = Ideal.span {algebraMap B.A (Localization M) d} ∧ algebraMap B.A (Localization M) d ∈ nonZeroDivisors (Localization M) ∧ ∃ N : ℕ, ∀ (x : Localization M) (m : ℕ), (l : Localization M) ^ m * x ∈ Ideal.span {algebraMap B.A (Localization M) d} → (l : Localization M) ^ N * x ∈ Ideal.span {algebraMap B.A (Localization M) d} := by
  first | exact @GlobalTheory.BSP.locAway_span_nzd_bdd | exact GlobalTheory.BSP.locAway_span_nzd_bdd | (intros; apply GlobalTheory.BSP.locAway_span_nzd_bdd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularAndBoundedTorsionOfAdicTopologicalBasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_and_bounded_torsion_of_adicTopologicalBasis : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (Q : Type) [CommRing Q] (i : A →+* Q) (d : A) (N : ℕ) (ι : Type), d ∈ nonZeroDivisors A → (∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d}) → TopBasis i (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ι → i d ∈ nonZeroDivisors Q ∧ ∀ (x : Q) (m : ℕ), (l : Q) ^ m * x ∈ Ideal.span {i d} → (l : Q) ^ N * x ∈ Ideal.span {i d} := by
  first | exact @GlobalTheory.BSP.TopBasis.regular_and_torsion_bounded | exact GlobalTheory.BSP.TopBasis.regular_and_torsion_bounded | (intros; apply GlobalTheory.BSP.TopBasis.regular_and_torsion_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqOfIsAdicCompletionMapStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_eq_of_isAdicCompletionMap : ∀ (L : Type) [CommRing L] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (i : L →+* Q) (J : Ideal L) (JC : Ideal C), IsCompl i J → IsHausdorff JC C → ∀ (h h' : Q →+* C), J.map (h.comp i) ≤ JC → h.comp i = h'.comp i → h = h' := by
  first | exact @GlobalTheory.BSP.ringHom_eq_of_isCompl | exact GlobalTheory.BSP.ringHom_eq_of_isCompl | (intros; apply GlobalTheory.BSP.ringHom_eq_of_isCompl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledProductSpanLatticeEntriesAndSpan
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.TraceConjugationCover

theorem latT_entries_and_span : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (L : Fin m → FinExt l) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ), (∀ k g i j, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ (L k).1) → (∀ k, ∀ x ∈ t k, ∀ i j, x i j ∈ (L k).1) → (∀ k (x : Matrix (Fin a) (Fin a) (Om l)), (∀ i j, x i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l)))) → (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∀ k i j, x k i j ∈ (L k).1) ∧ ∀ x : Fin m → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (GlobalTheory.TraceConjugationCover.latT ρs t M : Set (Fin m → Matrix (Fin a) (Fin a) (Om l))) := by
  intro l _ Γ _ a m ρs L t M hρ ht hspan

  have hsm : ∀ k (c : ℤ_[l]) (y : Om l), y ∈ (L k).1 → c • y ∈ (L k).1 := by
    intro k c y hy
    rw [← IsScalarTower.algebraMap_smul ℚ_[l] c y]
    exact (L k).1.smul_mem hy
  let S : Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l)) :=
    { carrier := {x | ∀ k i j, x k i j ∈ (L k).1}
      add_mem' := fun {x y} hx hy k i j => by
        simpa using (L k).1.add_mem (hx k i j) (hy k i j)
      zero_mem' := fun k i j => by simpa using (L k).1.zero_mem
      smul_mem' := fun c x hx k i j => by
        simpa using hsm k c _ (hx k i j) }
  have hlM : ∀ k, ((l : Om l) ^ M) ∈ (L k).1 := fun k =>
    pow_mem (by simpa using (L k).1.natCast_mem l) M
  have hsingle : ∀ k (y : Matrix (Fin a) (Fin a) (Om l)), (∀ i j, y i j ∈ (L k).1) →
      Pi.single k y ∈ S := by
    intro k y hy k' i j
    by_cases h : k' = k
    · subst h; simpa using hy i j
    · simp [Pi.single_apply, h, (L k').1.zero_mem]
  have hle : latT ρs t M ≤ S := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩ k i j
      exact hρ k g i j
    · rw [latL, Submodule.span_le]
      intro z hz
      simp only [Set.mem_iUnion, Set.mem_image] at hz
      obtain ⟨k, y, hy, rfl⟩ := hz
      refine hsingle k _ fun i j => ?_
      simpa using (L k).1.mul_mem (hlM k) (ht k y hy i j)
  refine ⟨fun x hx => hle hx, ?_⟩
  intro x hx
  have hsing : ∀ k, ∀ y ∈ t k, Pi.single k y ∈
      Submodule.span ℚ_[l] (latT ρs t M : Set (Fin m → Matrix (Fin a) (Fin a) (Om l))) := by
    intro k y hy
    have hne : ((l : ℚ_[l]) ^ M) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    have hmem : Pi.single k ((l : Om l) ^ M • y) ∈ latT ρs t M :=
      Submodule.mem_sup_right (Submodule.subset_span (Set.mem_iUnion.2 ⟨k, y, hy, rfl⟩))
    have heq : (l : Om l) ^ M • y = ((l : ℚ_[l]) ^ M) • y := by
      rw [← algebraMap_smul (Om l) ((l : ℚ_[l]) ^ M) y]
      simp
    have : (Pi.single k y : Fin m → Matrix (Fin a) (Fin a) (Om l)) = ((l : ℚ_[l]) ^ M)⁻¹ • (Pi.single k ((l : Om l) ^ M • y) : Fin m → Matrix (Fin a) (Fin a) (Om l)) := by
      rw [heq, Pi.single_smul', inv_smul_smul₀ hne]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have hk : ∀ k, Pi.single k (x k) ∈
      Submodule.span ℚ_[l] (latT ρs t M : Set (Fin m → Matrix (Fin a) (Fin a) (Om l))) := by
    intro k
    have h1 := hspan k (x k) (hx k)
    have h2 : LinearMap.single ℚ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k (x k) ∈
        Submodule.map (LinearMap.single ℚ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k)
          (Submodule.span ℚ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l)))) :=
      Submodule.mem_map_of_mem h1
    rw [Submodule.map_span] at h2
    refine (Submodule.span_le.2 ?_) h2
    rintro _ ⟨y, hy, rfl⟩
    exact hsing k y hy
  rw [← Finset.univ_sum_single x]
  exact Submodule.sum_mem _ fun k _ => hk k

end GlobalTheory.TraceConjugationCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanSingletonClosedOfBoundedTorsionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_singleton_of_bounded_torsion_of_adic_limit : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (d : A) (N : ℕ), d ∈ nonZeroDivisors A → (∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d}) → IsAdicComplete (Ideal.span {(l : A)} ⊔ Ideal.span {d}) A → ∀ x : A, (∀ n : ℕ, ∃ z, x - d * z ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n) → x ∈ Ideal.span {d} := by
  first | exact @GlobalTheory.BSP.span_singleton_closed_of_bounded_torsion | exact GlobalTheory.BSP.span_singleton_closed_of_bounded_torsion | (intros; apply GlobalTheory.BSP.span_singleton_closed_of_bounded_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateFinitenessAllOfLocalTateDuality
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory

theorem finAll_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.FinAll D := by
  intro hT D i w hw C
  exact Formalism.MainNotions.LargeLevelLemmas.tate_h1_finite_of_all_coefficients _ _ _
    (GlobalTheory.T.finite_H1_period_datum hT (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw)
    (_root_.GlobalTheory.LitGood.litGoodO (D.nd.l i) C.LL)

end GlobalTheory
end

