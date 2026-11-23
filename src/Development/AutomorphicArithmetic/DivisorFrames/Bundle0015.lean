module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentMapsForThetaTriple
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsNeZeroLinearModelVacuumEqSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices

open GlobalTheory.LinCoords GlobalTheory.WeilM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem hTens_half (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (t : E →ₐ[F] Fv F v) {n d : ℕ}
    (JA : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    {x y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hx : At (evFin F v) x) (hx0 : x.map (piW t) = 0)
    (hy0 : y.map (piW t) = 0) : hTens (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) JA JB x y = 0 := by
  have hs : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have ht : (t.comp σ).comp σ = t := AlgHom.ext fun e => by simp [hs]
  unfold hTens
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun k _ =>
    Finset.sum_eq_zero fun l _ => ?_
  have h1 : piW t (x a b) = 0 := congrFun (congrFun hx0 a) b
  have h2 : piW t (y k l) = 0 := congrFun (congrFun hy0 k) l
  have hat : At (evFin F v) (x a b * JA a k * JB b l * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (y k l)) := fun u hu => by
    rw [← smul_mul_assoc, ← smul_mul_assoc, ← smul_mul_assoc, (at_mat_iff x).1 hx a b u hu, zero_mul, zero_mul, zero_mul]
  rw [eq_lift2 h t hat, map_mul, map_mul, map_mul, h1, map_mul (piW (t.comp σ)), piW_cA' (t.comp σ), ht, h2, zero_mul, zero_mul, zero_mul, mul_zero,
    lift2_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.exists_ne_zero_linearModel_vacuum_eq_smul :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
        (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
        W.IsSkew σ B r' s' → M.IsGood B.ψ →
        ∀ (v : HeightOneSpectrum (𝓞 F)) (t₁ t₀ : E →ₐ[F] Fv F v), (∀ x, t₀ x = t₁ (σ x)) →
        ∀ (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
          (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)),
        M.IsLin B.ψ (piW t₁) (piW t₀) (fun u => b.1 * u.map (piW t₁) * c.1) ι →
        ∃ z : ℂ, z ≠ 0 ∧ ∀ x : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x → x.map (piW t₀) = 0 →
          ι (M.vac v) (b.1 * x.map (piW t₁) * c.1) = if x ∈ latAtV X W v then z else 0 := by

  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM v t₁ t₀ ht b c ι hι
  obtain rfl : t₀ = t₁.comp σ := AlgHom.ext ht
  have hat := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  have hs : ∀ {t : E →ₐ[F] Fv F v} (ξ) {x y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}, At (evFin F v) x →
      x.map (piW t) = 0 → y.map (piW t) = 0 → GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ξ
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F W.J) x y = 0 := fun ξ x y hx hx0 hy0 => by
    unfold GlobalTheory.WeilM.symp
    rw [hTens_half hB.cm _ _ _ hx hx0 hy0, mul_zero, map_zero]
  obtain ⟨hSB, h0, θ, -, hθ⟩ := hM.vac v
  obtain ⟨hz, hv⟩ := GlobalTheory.BigDat.lagr_vac (GlobalTheory.BigNZ.isLagrModel_of_isLin hι) hSB h0 (latAtV X W v : Set _)
    (fun γ hγ hγ' => by
      have h1 := hθ γ hγ
      rcases hγ' with h | h <;>
        rwa [hs _ h.1 h.2 h.2, mul_zero, AddChar.map_zero_eq_one, one_smul] at h1)
    (fun z => by
      refine ⟨(b⁻¹.1 * z * c⁻¹.1).map fun p => GlobalTheory.LinCoords.lift2 hB.cm t₁ p 0,
        ⟨(GlobalTheory.LinCoords.at_mat_iff _).2 fun i j => GlobalTheory.LinCoords.at_lift2 _ _ _ _,
          Matrix.ext fun i j => GlobalTheory.LinCoords.piW_comp_lift2 _ _ _ _⟩, ?_⟩
      have e : ((b⁻¹.1 * z * c⁻¹.1).map fun p => GlobalTheory.LinCoords.lift2 hB.cm t₁ p 0).map (piW t₁) = b⁻¹.1 * z * c⁻¹.1 :=
        Matrix.ext fun i j => GlobalTheory.LinCoords.piW_lift2 _ _ _ _
      show b.1 * _ * c.1 = z
      rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul,
        Matrix.mul_one])
    (fun x hx h => by
      refine (GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X W r s r' s' hB hX hW v x hx.1).2 fun γ hγ => ?_
      obtain ⟨γ₁, h₁, γ₂, h₂, rfl, e₁, e₂⟩ := GlobalTheory.LatSplit.latAtV_decomp hB.cm X W v t₁ γ hγ
      have e : GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F W.J) x (γ₁ + γ₂) =
          GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F W.J) x γ₁ +
          GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F W.J) x γ₂ := by
        simp only [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, Matrix.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
      rw [e, hs _ hx.1 hx.2 e₁, zero_add]
      exact h γ₂ h₂ ⟨hat γ₂ h₂, e₂⟩)
  refine ⟨ι (M.vac v) 0, hz, fun x hx hx0 => ?_⟩
  rw [hv x ⟨hx, hx0⟩, Set.indicator_apply]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsStdFstNeZeroOfRankLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem units_mul_relation_rearrange_commRing {R : Type} [CommRing R] {ε : R} (h : ε * ε = ε) (n : ℕ) : (1 : R) = 1 - ε + ε * ε ^ n := by
  have : ε * ε ^ n = ε := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, h]
  rw [this]; ring

private theorem matrix_map_ringHom_add_smul_sandwich {R : Type} [CommRing R] {a b : ℕ} (βS : GL (Fin a) R) (βT : GL (Fin b) R) (ε : R)
    (J : Matrix (Fin b) (Fin a) R) :
    (βT⁻¹).val * (ε • (βT.val * J * (βS⁻¹).val)) * βS.val = ε • J := by
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul,
    Matrix.mul_one]

private theorem topL_smul_identity {R : Type} [CommRing R] {a b : ℕ} (hab : a ≤ b) (ε : R) :
    topL a (ε • (Matrix.of fun (i : Fin b) (j : Fin a) => if i.1 = j.1 then (1 : R) else 0)) =
      ε • (1 : Matrix (Fin a) (Fin a) R) := by
  ext i j
  unfold topL
  rw [dite_eq_left ⟨lt_of_lt_of_le i.2 hab, j.2⟩]
  simp [Matrix.one_apply, Fin.ext_iff]

theorem UpperTheory.exists_stdFst_ne_zero_of_rank_le :
    ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (ν : (AE D)ˣ →* Circle) (e : AE D) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (I : Ideal (𝓞 D.host.E)),
      S.rank ≤ T.rank → IsIdemSum e Z → ∃ x : WO S T, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT x ≠ 0 := by
  intro D S T βS βT ν e Z I hr he
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hεε : toEAf D e * toEAf D e = toEAf D e := by rw [← RingHom.map_mul, hee]
  let J : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.of fun i j => if i.1 = j.1 then 1 else 0
  let M : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := βT.val * J * (βS⁻¹).val
  choose w _ hw using fun i j => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_surj (D := D) (M i j)
  let x : WO S T := fun i j => e * w i j
  have hx : (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • M := by
    ext i j
    change toEAf D (e * w i j) = toEAf D e * M i j
    rw [RingHom.map_mul, hw]
  have hf : frMapO S T βS βT x = toEAf D e • J := by
    unfold frMapO
    rw [hx]
    exact matrix_map_ringHom_add_smul_sandwich βS βT (toEAf D e) J
  have hJ : ∀ i j, (toEAf D e • J) i j = if i.1 = j.1 then toEAf D e else 0 := fun i j => by
    change toEAf D e * (if i.1 = j.1 then 1 else 0) = _
    split_ifs
    · exact mul_one _
    · exact mul_zero _
  have h1 : IsHalf e x := fun i j => by
    change e * (e * w i j) = e * w i j
    rw [← mul_assoc, hee]
  have h2 : IsIntM (toEAf D e • J) := fun i j => by
    rw [hJ]
    split_ifs
    · exact hE
    · exact zero_mem _
  have h3 : ∀ i j, S.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I ((toEAf D e • J) i j) := fun i j hi => by
    have hj := j.2
    rw [hJ, if_neg (by omega)]
    exact ⟨zero_mem _, zero_mem _⟩
  have h4 : ∃ y, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (topL S.rank (toEAf D e • J)) y := by
    refine ⟨1, RingHom.map_one _, ?_, ?_⟩
    · rw [topL_smul_identity hr, Matrix.det_smul, Matrix.det_one, mul_one, Units.val_one, RingHom.map_one]
      exact units_mul_relation_rearrange_commRing hεε _
    · rw [inv_one, Units.val_one, RingHom.map_one]
      exact one_mem _
  refine ⟨x, ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  rw [hf, if_pos ⟨h1, h2, h3⟩]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar
  rw [dite_eq_left h4]
  exact Circle.coe_ne_zero _
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.FiniteComponentMemStabilizerOfStandardSectionNeZ
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.adjugate_mem_subring_of_mem {R : Type} [CommRing R] (O : Subring R) {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i j, A i j ∈ O) : ∀ i j, A.adjugate i j ∈ O := by
  intro i j
  let A' : Matrix (Fin n) (Fin n) O := fun i j => ⟨A i j, hA i j⟩
  have eA : A.adjugate = O.subtype.mapMatrix A'.adjugate := by
    rw [show A = O.subtype.mapMatrix A' from rfl]
    exact (RingHom.map_adjugate O.subtype A').symm
  rw [eA]
  exact (A'.adjugate i j).2

private theorem UpperTheory.idempotent_smul_integral {R : Type} [CommRing R] (O : Subring R) {n : ℕ} (A M : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, (A * M) i j ∈ O) (ε y yi : R) (hε : ε * ε = ε) (hεO : ε ∈ O) (hyi : yi ∈ O)
    (hy : y = 1 - ε + ε * A.det) (hyy : y * yi = 1) : ∀ i j, (ε • M) i j ∈ O := by
  intro i j
  have h0 : yi * ε * A.det = ε := by
    subst hy
    linear_combination ε * hyy + (yi - yi * A.det) * hε
  have h1 : ε • M = (yi * ε) • (A.adjugate * (A * M)) := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul, h0]
  rw [h1, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  exact mul_mem (mul_mem hyi hεO)
    (Subring.sum_mem _ fun l _ => mul_mem (UpperTheory.adjugate_mem_subring_of_mem O A hA i l) (hB l j))

private theorem UpperTheory.upperRows_mul_right {D : D7} {b a : ℕ} (N : Matrix (Fin b) (Fin a) (Lev.EAf D))
    (κ : Matrix (Fin a) (Fin a) (Lev.EAf D)) : topL a (N * κ) = topL a N * κ := by
  ext i j
  simp only [topL, Matrix.mul_apply]
  by_cases hi : i.1 < b
  · simp [hi]
  · simp [hi]

private theorem UpperTheory.topL_integral {D : D7} {b a : ℕ} (N : Matrix (Fin b) (Fin a) (Lev.EAf D))
    (hN : IsIntM N) : IsIntM (topL a N) := by
  intro i j
  simp only [topL]
  split_ifs
  · exact hN _ _
  · exact zero_mem _

private theorem UpperTheory.idempotent_unit_det_integral {D : D7} {e : AE D} {Z : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e Z) {n : ℕ}
    (A M : Matrix (Fin n) (Fin n) (Lev.EAf D)) (hA : IsIntM A) (hB : IsIntM (A * M)) (y : (AE D)ˣ)
    (hy : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e A y) : IsIntM (toEAf D e • M) := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hyy : toEAf D (y : AE D) * toEAf D ((y⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  exact UpperTheory.idempotent_smul_integral _ A M hA hB _ _ _ hε hE hy.2.2 hy.2.1 hyy

private theorem UpperTheory.standard_section_integral_unit {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (x : WO S T)
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT x ≠ 0) :
    IsIntM (frMapO S T βS βT x) ∧ ∃ y, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (topL S.rank (frMapO S T βS βT x)) y := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst at hx
  split_ifs at hx with hc
  · refine ⟨hc.2.1, ?_⟩
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar at hx
    split_ifs at hx with hG
    · exact hG
    · exact absurd rfl hx
  · exact absurd rfl hx

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
private theorem UpperTheory.integral_unit_det_both {D : D7} {e : AE D} {Z : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e Z) {m n : ℕ}
    (N : Matrix (Fin m) (Fin n) (Lev.EAf D)) (γ : GL (Fin n) (Lev.EAf D)) (hI : IsIntM N)
    (hI' : IsIntM (HMul.hMul N (γ⁻¹ : GL (Fin n) (Lev.EAf D)).val)) (y y' : (AE D)ˣ)
    (hy : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (topL n N) y)
    (hy' : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (topL n (HMul.hMul N (γ⁻¹ : GL (Fin n) (Lev.EAf D)).val)) y') :
    IsIntM (toEAf D e • γ.val) ∧ IsIntM (toEAf D e • (γ⁻¹ : GL (Fin n) (Lev.EAf D)).val) := by
  have hA := UpperTheory.topL_integral N hI
  have hB := UpperTheory.topL_integral _ hI'
  constructor
  · refine UpperTheory.idempotent_unit_det_integral he _ _ hB ?_ y' hy'
    rw [UpperTheory.upperRows_mul_right, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    exact hA
  · refine UpperTheory.idempotent_unit_det_integral he _ _ hA ?_ y hy
    rw [← UpperTheory.upperRows_mul_right]
    exact hB

set_option maxHeartbeats 1000000 in
theorem UpperTheory.finiteComponent_mem_stabilizer_of_standardSection_ne_zero :
    ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (ν : (AE D)ˣ →* Circle) (e : AE D) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (I : Ideal (𝓞 D.host.E)),
      IsSelfDualC S ΛS → Formalism.L2.DIV.IsFrame βS ΛS → S.rank ≤ T.rank → IsIdemSum e Z → ∀ g : GA D S,
      (∀ v, (∀ PP ∈ Z, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig S.gram ΛS v) →
      ∀ x : WO S T, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT (actO S T g 1 x) ≠ 0 →
        Lev.finE S g ∈ Formalism.L2.DIV.St βS := by
  intro D S T ΛS βS βT ν e Z I hsd hfr hrk hZe g hg x hx hx'
  obtain ⟨hI, y, hy⟩ := UpperTheory.standard_section_integral_unit S T βS βT ν e I x hx
  obtain ⟨hI', y', hy'⟩ := UpperTheory.standard_section_integral_unit S T βS βT ν e I _ hx'
  have hu' := GlobalTheory.T.frameMatrix_weilPairAction_left_inv D S T βS βT g x
  rw [hu'] at hI' hy'
  obtain ⟨h1, h2⟩ := UpperTheory.integral_unit_det_both hZe _ (βS⁻¹ * Lev.finE S g * βS) hI hI' y y' hy hy'
  have hUA := GlobalTheory.LevSplit.finE_mem_UA S g
  obtain ⟨h3, h4⟩ := _root_.GlobalTheory.ConjIntegral.conj_smul_isIntM S ΛS βS hsd hfr _ hUA _ rfl e h1 h2
  obtain ⟨hεε, hεc⟩ := _root_.GlobalTheory.IdemConjSum.idemSum_add_conj_idem Z e hZe
  obtain ⟨k, hk, hmt⟩ := _root_.GlobalTheory.GfCut.exists_cut S (GlobalTheory.LevelNbhd.finPartG S g) (e + cA D e)
    (GlobalTheory.LevelNbhd.finPartG_mem_GfC S g) hεε hεc
  have hfk := _root_.GlobalTheory.FineCut.finE_cut S βS _ k (e + cA D e) hmt
  rw [GlobalTheory.SuppLevO.finE_finPartG] at hfk
  obtain ⟨hSt, -⟩ := _root_.GlobalTheory.FrameIdem.cut_mem_St_red S.rank βS _ _ Z e hZe h1 h2 h3 h4 hfk
  have hcomp : ∀ PP ∈ Z, GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) k =
      GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g := fun PP hP => by
    rw [← GlobalTheory.SuppLevO.proj_finPartG S g]
    exact _root_.GlobalTheory.CompIdem.projV_eq_of_idem S _ _ k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one Z e hZe PP hP) hmt
  have hkloc := (_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D S βS ΛS hfr k).1 hSt
  refine (_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D S βS ΛS hfr g).2 fun v => ?_
  by_cases hv : ∃ PP ∈ Z, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
  · obtain ⟨PP, hP, rfl⟩ := hv
    rw [← hcomp PP hP]
    exact hkloc _
  · push_neg at hv
    exact hg v hv
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.IsUnitDetProdDetIdlOfMemSt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem prod_orthogonal_idempotents {R ι : Type} [CommRing R] [DecidableEq ι] (d : R) (es : ι → R) (Z : Finset ι)
    (ho : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → es i * es j = 0) :
    ∏ w ∈ Z, (es w * d + (1 - es w)) = (∑ w ∈ Z, es w) * d + (1 - ∑ w ∈ Z, es w) := by
  induction Z using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ih fun i hi j hj hij => ho i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij]
    have h0 : es a * ∑ w ∈ s, es w = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj =>
        ho a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj) fun h => ha (h ▸ hj)
    linear_combination (d - 1) ^ 2 * h0

private theorem inv_aux {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Aˣ) (ε d d' : B)
    (hε : ε * ε = ε) (hd : d * d' = 1) (hx : f (x : A) = 1 - ε + ε * d) :
    f ((x⁻¹ : Aˣ) : A) = 1 - ε + ε * d' := by
  have h1 : f ((x⁻¹ : Aˣ) : A) * f (x : A) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have h2 : f (x : A) * (1 - ε + ε * d') = 1 := by
    rw [hx]; linear_combination (1 - d - d' + d * d') * hε + ε * hd
  calc f ((x⁻¹ : Aˣ) : A) = f ((x⁻¹ : Aˣ) : A) * (f (x : A) * (1 - ε + ε * d')) := by rw [h2, mul_one]
    _ = _ := by rw [← mul_assoc, h1, one_mul]

private theorem det_conj_eq {n : ℕ} {B : Type} [CommRing B] (β γ : GL (Fin n) B) :
    (β⁻¹ * γ * β : GL (Fin n) B).val.det = γ.val.det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj']

theorem UpperTheory.isUnitDet_prod_detIdl_of_mem_St :
    ∀ (D : D7) (S : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (e : AE D) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)),
      IsIdemSum e Z → ∀ g : GA D S, Lev.finE S g ∈ Formalism.L2.DIV.St βS →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val
        (∏ w ∈ Z, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g) := by
  classical
  intro D S βS e Z hZ g hg
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum hZ
  have hee : e * e = e := GlobalTheory.Tow.idemSum_mul_of_subset hZ hZ (Finset.Subset.refl Z)
  have hint := GlobalTheory.IdemRes.toEAf_mem_of_finPart
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee]))
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hZ
  have hid : ∀ w ∈ Z, GlobalTheory.RowVacScalar.idemAt w = es w := fun w hw =>
    GlobalTheory.Tow.idemAt_unique
      (Classical.epsilon_spec (p := fun a : AE D => Formalism.L2.NTheta.IsIdemAt a w) ⟨es w, hes w hw⟩) (hes w hw)
  have hval : ((∏ w ∈ Z, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g : (AE D)ˣ) : AE D)
      = e * (Formalism.L2.Theta.mt S g).det + (1 - e) := by
    rw [Units.coe_prod, hsum, ← prod_orthogonal_idempotents _ es Z fun i hi j hj hij => GlobalTheory.Tow.idemAt_orth (hes i hi) (hes j hj) hij]
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [hid w hw, GlobalTheory.RowVacScalar.detIdl_val (hes w hw).1.1]
  have hdet : toEAf D (Formalism.L2.Theta.mt S g).det = (Lev.finE S g).val.det := by
    rw [RingHom.map_det]; rfl
  have h2 : toEAf D ((∏ w ∈ Z, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g : (AE D)ˣ) : AE D)
      = 1 - toEAf D e + toEAf D e * (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val.det := by
    rw [hval, det_conj_eq, map_add (f := _), map_mul, map_sub, map_one, hdet, add_comm]
  refine ⟨?_, h2, ?_⟩
  · rw [hval, map_add (f := _), map_mul, map_sub, map_one, hinf, zero_mul, zero_add, sub_zero]
  · obtain ⟨z, hz⟩ := hg
    have hz' : (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)) = Formalism.L2.DIV.intGL _ _ _ z := by
      rw [← hz]
      show βS⁻¹ * (βS * Formalism.L2.DIV.intGL _ _ _ z * βS⁻¹) * βS = _
      group
    have hzd : (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val.det
        = (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype z.val.det := by
      rw [hz', RingHom.map_det]; rfl
    have hd : (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val.det *
        (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype (z⁻¹).val.det = 1 := by
      rw [hzd, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one]
    rw [inv_aux (toEAf D) _ _ _ _ (by rw [← map_mul, hee]) hd h2]
    exact add_mem (sub_mem (one_mem _) hint) (mul_mem hint (z⁻¹).val.det.2)
end

