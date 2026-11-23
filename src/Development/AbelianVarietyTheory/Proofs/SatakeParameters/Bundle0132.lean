module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Development.AutomorphicArithmetic.OrbitLabellings.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleWdEigenEqualNorm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IrrWeilAbs

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_pow_central {n : ℕ} (a : WDRep h (Fin n → ℂ)) {φ : Weil h} (hφ : deg φ = 1) :
    ∃ m : ℕ, 0 < m ∧ ∀ σ : Weil h, a.ρ (φ ^ m) * a.ρ σ = a.ρ σ * a.ρ (φ ^ m) := by
  classical
  let S : Set (Module.End ℂ (Fin n → ℂ)) := Set.range fun τ : Ine (F := E) A => a.ρ (ineIncl h τ)
  haveI : Finite S := a.smooth.finite_range.to_subtype
  have conj_mem : ∀ (k : ℕ), ∀ s ∈ S, a.ρ (φ ^ k) * s * a.ρ ((φ ^ k)⁻¹) ∈ S := by
    rintro k _ ⟨τ, rfl⟩
    have h0 : deg (φ ^ k * ineIncl h τ * (φ ^ k)⁻¹) = 0 := by simp
    refine ⟨⟨_, deg_eq_zero_iff.mp h0⟩, ?_⟩
    simp only [← map_mul]
    exact congrArg a.ρ (Subtype.ext rfl)
  let g : ℕ → (S → S) := fun k s => ⟨_, conj_mem k s.1 s.2⟩
  obtain ⟨k1, k2, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite g
  obtain ⟨k, m, hm, hkm⟩ : ∃ k m : ℕ, 0 < m ∧ g k = g (k + m) := by
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact ⟨k1, k2 - k1, by omega, by rw [show k1 + (k2 - k1) = k2 by omega]; exact heq⟩
    · exact ⟨k2, k1 - k2, by omega, by rw [show k2 + (k1 - k2) = k1 by omega]; exact heq.symm⟩
  have comm_ine : ∀ τ : Ine (F := E) A,
      a.ρ (φ ^ m) * a.ρ (ineIncl h τ) = a.ρ (ineIncl h τ) * a.ρ (φ ^ m) := by
    intro τ
    have e1 : a.ρ (φ ^ k * ineIncl h τ * (φ ^ k)⁻¹) =
        a.ρ (φ ^ (k + m) * ineIncl h τ * (φ ^ (k + m))⁻¹) := by
      have := congrArg Subtype.val (congrFun hkm ⟨_, τ, rfl⟩)
      rw [map_mul, map_mul, map_mul, map_mul]
      exact this
    have e2 := congrArg (fun X => a.ρ ((φ ^ k)⁻¹) * X * a.ρ (φ ^ k * φ ^ m)) e1
    simp only [← map_mul] at e2
    rw [← map_mul, ← map_mul]
    convert e2.symm using 2 <;> group
  refine ⟨m, hm, fun σ => ?_⟩
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul hφ σ
  have hc : φ ^ m * φ ^ deg σ = φ ^ deg σ * φ ^ m :=
    ((Commute.refl φ).pow_left m).zpow_right (deg σ)
  rw [hτ, map_mul, ← mul_assoc, ← map_mul, hc, map_mul, mul_assoc, comm_ine, ← mul_assoc]

theorem exists_smul_of_commute {n : ℕ} (a : WDRep h (Fin n → ℂ)) (hirr : a.ρ.IsIrreducible)
    (P : Module.End ℂ (Fin n → ℂ)) (hP : ∀ σ : Weil h, P * a.ρ σ = a.ρ σ * P) :
    ∃ c : ℂ, ∀ v, P v = c • v := by
  haveI := hirr
  let f : Representation.IntertwiningMap a.ρ a.ρ :=
    ⟨P, fun σ => LinearMap.ext fun v => LinearMap.congr_fun (hP σ) v⟩
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := a.ρ)).2 f
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun F : Representation.IntertwiningMap a.ρ a.ρ => F v) hc
  rw [Algebra.algebraMap_eq_smul_one] at this
  simpa [f] using this.symm

theorem irrWD_eig_norm_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ = ‖β‖ := by
  intro E Ω _ _ _ _ _ A w h x hx φ hφ α hα β hβ
  obtain ⟨n, a, rfl, hirr⟩ := hx
  rw [WD.eig_mk] at hα hβ
  obtain ⟨m, hm, hcomm⟩ := exists_pow_central a hφ
  obtain ⟨c, hc⟩ := exists_smul_of_commute a hirr _ hcomm
  have hev : ∀ γ ∈ (a.ρ φ).charpoly.roots, γ ^ m = c := by
    intro γ hγ
    obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
      (Polynomial.isRoot_of_mem_roots hγ)).exists_hasEigenvector
    have hpow : ∀ k : ℕ, ((a.ρ φ) ^ k) v = γ ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv.apply_eq_smul, smul_smul, pow_succ]
    have h1 : γ ^ m • v = c • v := by rw [← hpow, ← map_pow, hc]
    exact smul_left_injective ℂ hv.2 h1
  have h2 : ‖α‖ ^ m = ‖β‖ ^ m := by rw [← norm_pow, ← norm_pow, hev α hα, hev β hβ]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hm.ne').mp h2

end GlobalTheory.IrrWeilAbs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConj
section
noncomputable section

open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CsdFromConj

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

theorem invTOp_invTOp (o : Op L a) : invTOp (invTOp o) = o := by
  cases o with
  | fin k => exact congrArg Op.fin (Units.ext (Matrix.transpose_transpose k.val))
  | cpt k =>
    refine congrArg Op.cpt (Subtype.ext ?_)
    ext i j : 1
    simp [barK, Matrix.star_apply]
  | lie X =>
    refine congrArg Op.lie ?_
    funext i j
    simp [toL, Function.swap, Pi.neg_apply]

theorem invT_map {R : Type} [CommRing R] (c : R →+* R) (g : GL (Fin a) R) :
    invT a R (GeneralLinearGroup.map c g) = GeneralLinearGroup.map c (invT a R g) :=
  Units.ext (by rw [show (invT a R (GeneralLinearGroup.map c g)).val = ((GeneralLinearGroup.map c g)⁻¹).valᵀ from rfl,
    ← map_inv]; rfl)


omit [NumberField L] [IsCMField L] in
theorem barK_barK (k : Kinf L a) : barK (barK k) = k := by
  refine Subtype.ext ?_
  ext i j : 1
  simp [barK, Matrix.star_apply]

def phiG (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) : GA L a :=
  finGL L a (PhiU a (Af L)) * infGL L a (Unitary.toUnits (PhiK L a))

theorem toUnits_PhiK : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl

theorem act_thetaOp (o : Op L a) :
    act (thetaOp o) * rt L a (phiG L a) = rt L a (phiG L a) * act (conjOp (invTOp o)) := by
  cases o with
  | fin k =>
    change rt L a (finGL L a _) * rt L a (phiG L a) = rt L a (phiG L a) * rt L a (finGL L a _)
    rw [← map_mul, ← map_mul]
    congr 1
    refine ga_ext ?_ ?_
    · simp [phiG, map_mul]
    · simp only [phiG, map_mul, pFin_finGL, pFin_infGL, mul_one]
      rw [thetaGL, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, invT_map]
      simp [mul_assoc]
  | cpt k =>
    change rt L a (infGL L a (Unitary.toUnits _)) * rt L a (phiG L a) =
      rt L a (phiG L a) * rt L a (infGL L a (Unitary.toUnits _))
    rw [← map_mul, ← map_mul]
    congr 1
    rw [barK_barK]
    refine ga_ext ?_ ?_
    · simp [phiG, map_mul, map_inv]
    · simp [phiG, map_mul]
  | lie X =>
    have hY : (fun i j => star (toL (-(Matrix.of X)ᵀ) i j) : Lie L a) = toL (-(Matrix.of X)ᴴ) := by
      funext i j
      simp [toL, Matrix.conjTranspose_apply]
    have hR := GlobalTheory.CapAdInv.rt_lie (PhiU a (Cinf L)) (-(Matrix.of X)ᴴ)
    have e : (PhiU a (Cinf L)).val * -(Matrix.of X)ᴴ * ((PhiU a (Cinf L))⁻¹).val =
        -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) := by
      rw [Matrix.mul_neg, Matrix.neg_mul]; rfl
    rw [e] at hR
    change lie L a _ * rt L a (phiG L a) = rt L a (phiG L a) * lie L a (fun i j => star (toL (-(Matrix.of X)ᵀ) i j))
    rw [hY, phiG, map_mul, toUnits_PhiK, mul_assoc (rt L a (finGL L a _)), hR, ← mul_assoc (rt L a (finGL L a _)),
      ← lie_rt_fin, mul_assoc (lie L a _)]

theorem rt_phiG : rt L a (phiG L a) = act (.fin (PhiU a (Af L))) * act (.cpt (PhiK L a)) := map_mul _ _ _

theorem act_fin_inv (k : GL (Fin a) (Af L)) : act (.fin k) * act (.fin k⁻¹) = 1 := by
  change finRep L a k * finRep L a k⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

theorem act_fin_inv' (k : GL (Fin a) (Af L)) : act (.fin k⁻¹) * act (.fin k) = 1 := by
  change finRep L a k⁻¹ * finRep L a k = 1
  rw [← map_mul, inv_mul_cancel, map_one]

theorem act_cpt_inv (k : Kinf L a) : act (.cpt k) * act (.cpt k⁻¹) = 1 := by
  change cptRep L a k * cptRep L a k⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

theorem act_cpt_inv' (k : Kinf L a) : act (.cpt k⁻¹) * act (.cpt k) = 1 := by
  change cptRep L a k⁻¹ * cptRep L a k = 1
  rw [← map_mul, inv_mul_cancel, map_one]

def phiEquiv (π : CuspSub L a) : π.V ≃ₗ[ℂ] π.V :=
  LinearEquiv.ofLinear (π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a)))
    (π.op (.cpt (PhiK L a)⁻¹) * π.op (.fin (PhiU a (Af L))⁻¹))
    (LinearMap.ext fun φ => Subtype.ext <| by
      change act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) (act (.cpt (PhiK L a)⁻¹)
        (act (.fin (PhiU a (Af L))⁻¹) φ.1))) = φ.1
      rw [← Module.End.mul_apply (act (.cpt (PhiK L a))), act_cpt_inv, Module.End.one_apply,
        ← Module.End.mul_apply, act_fin_inv, Module.End.one_apply])
    (LinearMap.ext fun φ => Subtype.ext <| by
      change act (.cpt (PhiK L a)⁻¹) (act (.fin (PhiU a (Af L))⁻¹) (act (.fin (PhiU a (Af L)))
        (act (.cpt (PhiK L a)) φ.1))) = φ.1
      rw [← Module.End.mul_apply (act (.fin (PhiU a (Af L))⁻¹)), act_fin_inv', Module.End.one_apply,
        ← Module.End.mul_apply, act_cpt_inv', Module.End.one_apply])

theorem op_thetaOp_phiEquiv (π : CuspSub L a) (o : Op L a) (φ : π.V) :
    π.op (thetaOp o) (phiEquiv π φ) = phiEquiv π (π.op (conjOp (invTOp o)) φ) := Subtype.ext <| by
  change act (thetaOp o) (act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) φ.1)) =
    act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) (act (conjOp (invTOp o)) φ.1))
  have h := LinearMap.congr_fun (act_thetaOp (L := L) (a := a) o) φ.1
  rw [rt_phiG] at h
  exact h

theorem isCsd_of_invT_conj (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a)
    (S : π.V ≃ₗ[ℂ] π.V) (hS : ∀ o φ, S (π.op (invTOp o) φ) = π.op (conjOp o) (S φ)) : π.IsCsd := by
  refine ⟨(phiEquiv π).symm.trans S.symm, fun o φ => ?_⟩
  obtain ⟨χ, rfl⟩ := (phiEquiv π).surjective φ
  obtain ⟨ψ, rfl⟩ := S.surjective χ
  have h := hS (invTOp o) ψ
  rw [invTOp_invTOp] at h
  simp only [LinearEquiv.trans_apply, op_thetaOp_phiEquiv, LinearEquiv.symm_apply_apply, ← h]

end GlobalTheory.CsdFromConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LexSumSplitFirstBlockStrictMono
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem lexSumSplit_strictMono : ∀ (s : ℕ) (t : Fin (s + 1) → ℕ), StrictMono fun c : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)) => (Sum.elim (fun j => toLex (⟨0, j⟩ : Σ a, Fin (t a))) (fun x => toLex (⟨(ofLex x).1.succ, (ofLex x).2⟩ : Σ a, Fin (t a))) (ofLex c) : Σₗ a, Fin (t a)) := by
  intro s t a b hab
  induction a using Lex.rec with | _ a => ?_
  induction b using Lex.rec with | _ b => ?_
  rcases a with j | x <;> rcases b with j' | x'
  · have h : j < j' := Sum.Lex.inl_lt_inl_iff.mp hab
    simp only [ofLex_toLex, Sum.elim_inl]
    exact Sigma.Lex.right _ _ h
  · simp only [ofLex_toLex, Sum.elim_inl, Sum.elim_inr]
    exact Sigma.Lex.left _ _ (Fin.succ_pos _)
  · exact absurd hab (not_lt_of_gt (Sum.Lex.inl_lt_inr _ _))
  · have h : x < x' := Sum.Lex.inr_lt_inr_iff.mp hab
    simp only [ofLex_toLex, Sum.elim_inr]
    induction x using Lex.rec with | _ x => ?_
    induction x' using Lex.rec with | _ x' => ?_
    rcases x with ⟨i, j⟩
    rcases x' with ⟨i', j'⟩
    change Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨i, j⟩ : Σ a : Fin s, Fin (t a.succ)) ⟨i', j'⟩ at h
    change Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨i.succ, j⟩ : Σ a, Fin (t a)) ⟨i'.succ, j'⟩
    rcases h with ⟨_, _, hi⟩ | ⟨_, _, hj⟩
    · exact Sigma.Lex.left _ _ (Fin.succ_lt_succ_iff.mpr hi)
    · exact Sigma.Lex.right _ _ hj

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LowTermLeSecondRealPlaceBounds
section
noncomputable section

namespace GlobalTheory.TwU.LowTerm

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

variable {D : D7} {L : SizeData₂ D}

theorem sum_betaI (X : Inst D L) (K : Consts) (ce : ErrC) (j p : ℕ) (hs : ¬ IsSg D p) :
    ∑ r ∈ OrbitPlaces.repsPl X p, OrbitPlaces.betaI X K ce j p r =
      (∑ t ∈ reps X p, max (g0 X K (aL L) (bL L) p j t) 0) +
        ∑ t ∈ reps X p, (FOrb D j p (true, t) - OrbitPlaces.errF L K ce j p (true, t)) := by
  have hd : Disjoint ((reps X p).image (fun t => ((false, t) : OrbitPlaces.Pl D)))
      ((reps X p).image (fun t => ((true, t) : OrbitPlaces.Pl D))) := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨t', -, h⟩ := Finset.mem_image.1 h2
    simp at h
  unfold OrbitPlaces.repsPl
  rw [if_neg hs, Finset.sum_union hd, Finset.sum_image (fun a _ b _ h => by simpa using h),
    Finset.sum_image (fun a _ b _ h => by simpa using h)]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp [OrbitPlaces.betaI, OrbitPlaces.g0Pl, kindA, hs]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp [OrbitPlaces.betaI, OrbitPlaces.g0Pl, kindA]

theorem FInert_sub_EatI (X : Inst D L) (K : Consts) (ce : ErrC) {p j : ℕ} (hp : p.Prime) (hc : IsResidueClassZero D p)
    (hh : HEv D p) (hs : ¬ IsSg D p) (hj : j ∈ SizeData₂.lifts D) :
    FInert D j p - EatI L K ce j p ≤
      ∑ t ∈ reps X p, (FOrb D j p (true, t) - OrbitPlaces.errF L K ce j p (true, t)) := by
  have h := OrbitPlaces.sumI X K ce p hp (Or.inl ⟨hc, hh⟩) j hj
  rw [sum_betaI X K ce j p hs] at h
  linarith

theorem sum_dG_le {m n : ℕ} (hm : 1 ≤ m) {d : ℕ → ℕ} (h0 : d 0 = 0) (hj : ∀ j, d j ≤ n) :
    ∑ j ∈ Finset.range m, (d j : ℝ) ≤ ((m : ℝ) - 1) * n := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ', h0]
  have : ∑ j ∈ Finset.range k, (d (j + 1) : ℝ) ≤ ∑ _j ∈ Finset.range k, (n : ℝ) :=
    Finset.sum_le_sum fun j _ => by exact_mod_cast hj _
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  push_cast
  linarith

theorem lowS_le : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC)
    (Xe : ErrX D) (dG : ℕ → ℕ), L.FDef → dG 0 = 0 →
    (∀ j, dG j ≤ padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam) →
    WeilJacquetShalikaLaw.lowS L Xe K ce 1 u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m, ∑ t ∈ reps X (D.what₂.places.resChar w),
      if ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n then
        FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0) -
      ∑ j ∈ Finset.range D.R.m, (dG j : ℝ) := by
  intro D u w hg L X K ce Xe dG hF h0 hd
  have hm : 1 ≤ D.R.m := le_trans one_le_two D.R.two_le_m
  have hloss := sum_dG_le hm h0 hd
  have hc : IsResidueClassZero D (D.what₂.places.resChar w) := hg.2.2.1
  have hs : ¬ IsSg D (D.what₂.places.resChar w) := by
    intro h
    have h' : D.host.cls (D.what₂.places.resChar w) = _ := h
    rw [hg.2.2.1] at h'
    exact absurd h' (by decide)
  have hev : HEv D (D.what₂.places.resChar w) := hEv_of_hNeZero hg.1 hg.2.2.2.1
  have hh := hev.ne_zero
  have hne : ∀ i : Fin 2, D.what₂.places.resChar w ≠ D.host.g i := fun i h => hg.2.2.2.2.1 (h ▸ D.host.g_level i)
  have h2 : D.host.cls (D.what₂.places.resChar w) ≠ PrimeClass.ramD := by rw [hg.2.2.1]; decide
  have h4 : D.what₂.places.resChar w ∉ L.gTypes := by simp [SizeData₂.gTypes, hne]
  have hcard : ((SizeData₂.lifts D).card : ℝ) = D.R.m := by simp [SizeData₂.lifts]
  have hterm : ∀ j ∈ SizeData₂.lifts D, L.F j w - WeilJacquetShalikaLaw.ES L Xe K ce u j w =
      (if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
        FInert D j (D.what₂.places.resChar w) - EatI L K ce j (D.what₂.places.resChar w) else 0) - WeilJacquetShalikaLaw.vDG D u w := by
    intro j hj
    rw [hF j hj w]
    unfold Fval FvalP WeilJacquetShalikaLaw.ES Eval WeilJacquetShalikaLaw.vDG
    simp only [if_neg (hne 0), if_neg (hne 1), if_neg (WeilJacquetShalikaLaw.residue_char_ne_level hg), if_neg h2, if_neg h4]
    by_cases hX : (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n
    · have hA : (IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
          (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n := ⟨Or.inl hc, hX⟩
      have hB : ¬ (IsResidueClassZero D (D.what₂.places.resChar w) ∧ hP D (D.what₂.places.resChar w) = 0) := fun h => hh h.2
      simp only [if_pos hA, if_neg hB, if_pos hX]
      unfold FInert
      rw [if_neg hB]
      ring
    · have hA : ¬ ((IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
          (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n) := fun h => hX h.2
      simp only [if_neg hA, if_neg hX]
      ring
  have hsum : WeilJacquetShalikaLaw.lowS L Xe K ce 1 u w = (∑ j ∈ Finset.Icc 1 D.R.m,
      if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
        FInert D j (D.what₂.places.resChar w) - EatI L K ce j (D.what₂.places.resChar w) else 0) -
      ((D.R.m : ℝ) - 1) * WeilJacquetShalikaLaw.vDG D u w := by
    unfold WeilJacquetShalikaLaw.lowS
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    have hl : SizeData₂.lifts D = Finset.Icc 1 D.R.m := rfl
    rw [hl]
    ring
  have hle : (∑ j ∈ Finset.Icc 1 D.R.m,
      if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
        FInert D j (D.what₂.places.resChar w) - EatI L K ce j (D.what₂.places.resChar w) else 0) ≤
      ∑ j ∈ Finset.Icc 1 D.R.m, ∑ t ∈ reps X (D.what₂.places.resChar w),
        if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
          FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0 := by
    refine Finset.sum_le_sum fun j hj => ?_
    by_cases hX : (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n
    · simp only [if_pos hX]
      exact FInert_sub_EatI X K ce hg.1 hc hev hs hj
    · simp [hX]
  have hv : ((D.R.m : ℝ) - 1) * (padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℝ) =
      ((D.R.m : ℝ) - 1) * WeilJacquetShalikaLaw.vDG D u w := rfl
  rw [hsum]
  linarith

end GlobalTheory.TwU.LowTerm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharacterEigenProduct
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.DetSp

open Polynomial TensorProduct Module

theorem prod_roots_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) : f.charpoly.roots.prod = LinearMap.det f := by
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V), ← Matrix.det_eq_prod_roots_charpoly,
    LinearMap.det_toMatrix]

theorem det_map {n m : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (g : Module.End ℂ (Fin m → ℂ)) :
    LinearMap.det (TensorProduct.map f g) = LinearMap.det f ^ m * LinearMap.det g ^ n := by
  classical
  set b := Pi.basisFun ℂ (Fin n)
  set c := Pi.basisFun ℂ (Fin m)
  rw [← LinearMap.det_toMatrix (b.tensorProduct c), TensorProduct.toMatrix_map, Matrix.det_kronecker,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix, Fintype.card_fin, Fintype.card_fin]

theorem det_diagEnd {m : ℕ} (c : Fin m → ℂ) : LinearMap.det (diagEnd c) = ∏ i, c i := by
  classical
  have e : diagEnd c = Matrix.toLin' (Matrix.diagonal c) := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [Matrix.mulVec_diagonal]
  rw [e, LinearMap.det_toLin', Matrix.det_diagonal]

theorem sum_centred (m : ℕ) : ∑ i : Fin m, (((i : ℕ) : ℝ) - ((m : ℝ) - 1) / 2) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) - ((m : ℝ) - 1) / 2)), Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : ∀ k : ℕ, ∑ i ∈ Finset.range k, (i : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [this]; ring

variable {E : Type*} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem prod_qPow {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ s, qPow w (f i) = qPow w (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, qPow_add]

theorem prod_spEig (m : ℕ) : ∏ i, WDRep.spEig w m i = 1 := by
  simp only [WDRep.spEig]
  rw [prod_qPow, sum_centred, qPow_zero]

end GlobalTheory.WeilDeligne.DetSp

namespace GlobalTheory.WeilDeligne

theorem prod_eig_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h) (l : ℕ) (σ : Weil h), ((x.lpChar (WD.lpSp (h := h) l)).eig σ).prod = ((x.eig σ).prod) ^ l := by
  intro E Ω _ _ _ _ _ A w h x l σ
  induction x using WD.ind with
  | hP n a =>
    rw [WD.lpSp, WD.lpChar_mk, WD.eig_mk, WD.eig_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
      DetSp.prod_roots_charpoly, DetSp.prod_roots_charpoly, DetSp.det_map, DetSp.det_diagEnd,
      Finset.prod_zpow, ← Units.coe_prod, DetSp.prod_spEig, Units.val_one, one_zpow, one_pow, mul_one]

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
section
noncomputable section

namespace GlobalTheory.Hk3.HoweG

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def adj (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (x : Matrix (Fin n') (Fin n) L) :
    Matrix (Fin n) (Fin n') L :=
  ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ x * (JT : Matrix (Fin n') (Fin n') L)

def HomA (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L) : Prop :=
  (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) ∧
    ∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ (adj σ JS JT x *ᵥ w)) i ∈ Formalism.UG.intL L

def GramEq (σ : L →+* L) {n n' : ℕ} (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L) : Prop :=
  ∀ m m' : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → (∀ i, m' i ∈ Formalism.UG.intL L) → ∀ c ∈ Formalism.UG.intL L,
    (∀ i, (x *ᵥ (c • m)) i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ (c • m')) i ∈ Formalism.UG.intL L) →
      c * (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (y *ᵥ m) (y *ᵥ m') -
        Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (x *ᵥ m) (x *ᵥ m')) ∈ Formalism.UG.intL L

def SelfDual (σ : L →+* L) {n : ℕ} (JS : GL (Fin n) L) (a : GL (Fin n) L) : Prop :=
  (∀ i j, (Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) i j ∈
      Formalism.UG.intL L) ∧
    ∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L

end GlobalTheory.Hk3.HoweG

end
end

