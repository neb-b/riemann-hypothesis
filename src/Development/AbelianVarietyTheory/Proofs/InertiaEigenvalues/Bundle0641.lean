module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLatticePairsIndexRpowLe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeIndexSplitPlaceEqProductLocal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLatticeIndexSumLeZetaSqSubOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.SplitHecke

noncomputable section

namespace GlobalTheory.SplitIndexSum
open GlobalTheory.AdelicLatMove (mt_mul mt_one)

abbrev stdLat (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ) : Submodule O (Fin r → K) :=
  Submodule.span O (Set.range (Pi.basisFun K (Fin r)))

abbrev movLat (O K : Type) [CommRing O] [Field K] [Algebra O K] {r : ℕ} (h : GL (Fin r) K) : Submodule O (Fin r → K) :=
  (stdLat O K r).map (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)

theorem suppAt_mul {D : D7} {e : AE D} {V : HSp D} {g g' : GA D V} (hg : SuppAt e V g) (hg' : SuppAt e V g') :
    SuppAt e V (g * g') := by
  have h : (e + cA D e) • (mt V g - 1) = mt V g - 1 := Matrix.ext fun i j => hg i j
  have h' : (e + cA D e) • (mt V g' - 1) = mt V g' - 1 := Matrix.ext fun i j => hg' i j
  have h1 : mt V (g * g') - 1 = (mt V g - 1) * mt V g' + (mt V g' - 1) := by
    rw [mt_mul, Matrix.sub_mul, Matrix.one_mul]; abel
  have h2 : (e + cA D e) • (mt V (g * g') - 1) = mt V (g * g') - 1 := by
    rw [h1, smul_add, ← Matrix.smul_mul, h, h']
  exact fun i j => congrFun (congrFun h2 i) j

theorem chart_of_finIdem {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}
    (hv : IsFinIdem D v (e + cA D e)) (he : IsSplitIdem D e) : ∃ π : AE D →+* Fv D.host.F v, Chart e v π := by
  obtain ⟨v', π, hπ⟩ := _root_.GlobalTheory.SplitChart.exists_chart e he
  obtain ⟨ε, ⟨α, rfl, hα1, hα0⟩, hf⟩ := hv
  have hπe : π e = 1 := by
    have : π (1 - e) = 0 := (hπ.2.1 _).2 (by rw [mul_sub, mul_one, he.1, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  have hπc : π (cA D e) = 0 := (hπ.2.1 _).2 he.2.1
  have h1 : π (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 1 := by
    rw [← hf, map_add (f := _), hπe, hπc, add_zero]
  rw [hπ.2.2.1] at h1
  by_cases hvv : v' = v
  · subst hvv; exact ⟨π, hπ⟩
  · exfalso
    have h2 := hα0 v' hvv
    have h3 : sndA D.host.F (pairA D.host.F 0 α) = α := rfl
    rw [h3, h2] at h1
    exact zero_ne_one h1
theorem gInt_of_movLat_eq (O K : Type) [CommRing O] [Field K] [Algebra O K] {r : ℕ}
    (h h' : GL (Fin r) K) (hh : movLat O K h = movLat O K h') : GInt O (h⁻¹ * h') :=
  _root_.GlobalTheory.SplitHecke.gInt_inv_mul_of_map_eq O K r h h' hh

theorem latIndex_eq_split : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v),
    IsSplitIdem D e → Chart e v π → ∀ (W : HSp D) (β : GL (Fin W.rank) (Fv D.host.F v)), Frame W e π β →
    ∀ g : GA D W, SuppAt e W g →
      latIndex W g = (movLat (Ov D v) (Fv D.host.F v) (rho W π β g)).toAddSubgroup.relIndex
          (stdLat (Ov D v) (Fv D.host.F v) W.rank).toAddSubgroup *
        (stdLat (Ov D v) (Fv D.host.F v) W.rank).toAddSubgroup.relIndex
          (movLat (Ov D v) (Fv D.host.F v) (rho W π β g)).toAddSubgroup := by
  intro D e v π he hπ W β hβ g hg
  haveI := Formalism.UG.P.glint_finite_residueField (F := D.host.F) v
  rw [_root_.GlobalTheory.SplitIndexLocal.latIndex_split_local e v π he hπ W β hβ g hg, map_inv, _root_.GlobalTheory.IndexTranspose.relIndex_transpose_inv]

theorem indexSum_split : ∀ (D : D7) (W : HSp D) (n : ℕ), 2 * W.rank + 5 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) → ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') → ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ (∏ i ∈ Finset.range W.rank, (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ ((i : ℝ) - (n : ℝ) / 2))⁻¹) ^ 2 - 1 := by
  classical
  intro D W n hn v f hf ⟨e, he, hef⟩ C hC hdist
  subst hef
  obtain ⟨π, hπ⟩ := chart_of_finIdem hf he
  obtain ⟨β, hβ⟩ := GlobalTheory.SplitFrame.exists_frame e v π he hπ W
  haveI := Formalism.UG.P.glint_finite_residueField (F := D.host.F) v
  set O := Ov D v
  set K := Fv D.host.F v
  set σ : ℝ := (n : ℝ) / 2 with hσ
  have hsupp : ∀ g ∈ C, SuppAt e W g := fun g hg => (hC g hg).1
  let Φ : GL (Fin W.rank) K → ℝ := fun h =>
    ((((movLat O K h).toAddSubgroup.relIndex (stdLat O K W.rank).toAddSubgroup : ℕ) : ℝ) *
      (((stdLat O K W.rank).toAddSubgroup.relIndex (movLat O K h).toAddSubgroup : ℕ) : ℝ)) ^ (-σ)
  have hK : ∀ g, SuppAt e W g → (g ∈ KsphC W ∅ ↔ GInt O (rho W π β g)) :=
    GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt e v π he hπ W β hβ
  have hterm : ∀ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) = Φ (rho W π β g) := by
    intro g hg
    rw [latIndex_eq_split e v π he hπ W β hβ g (hsupp g hg), Nat.cast_mul, neg_div]
  have hinj : ∀ g ∈ C, ∀ g' ∈ C, movLat O K (rho W π β g) = movLat O K (rho W π β g') → g = g' := by
    intro g hg g' hg' hm
    have h1 := gInt_of_movLat_eq O K _ _ hm
    rw [← map_inv, ← map_mul] at h1
    exact hdist g hg g' hg' ((hK _ (suppAt_mul (GlobalTheory.SplitHecke.Stab.suppAt_inv (hsupp g hg)) (hsupp g' hg'))).2 h1)
  have hone : ∀ g ∈ C, movLat O K (1 : GL (Fin W.rank) K) ≠ movLat O K (rho W π β g) := by
    intro g hg hm
    have h1 := gInt_of_movLat_eq O K _ _ hm
    rw [inv_one, one_mul] at h1
    exact (hC g hg).2 ((hK g (hsupp g hg)).2 h1)
  have hnot : (1 : GL (Fin W.rank) K) ∉ C.image (rho W π β) := by
    intro h1
    obtain ⟨g, hg, hg1⟩ := Finset.mem_image.1 h1
    exact hone g hg (by rw [hg1])
  have hsum : ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) = ∑ h ∈ C.image (rho W π β), Φ h := by
    rw [Finset.sum_image (fun g hg g' hg' he' => hinj g hg g' hg' (congrArg (movLat O K) he'))]
    exact Finset.sum_congr rfl hterm
  have hΦ1 : Φ 1 = 1 := by
    have : movLat O K (1 : GL (Fin W.rank) K) = stdLat O K W.rank := by
      simp [movLat]
    simp only [Φ, this, AddSubgroup.relIndex_self, Nat.cast_one, mul_one, Real.one_rpow]
  have hσr : (W.rank : ℝ) - 1 < σ := by
    rw [hσ]; have : (2 * W.rank + 5 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hbig := _root_.GlobalTheory.LatticePairSum.sum_index_pairs_le O K W.rank σ hσr (insert 1 (C.image (rho W π β))) (by
    intro h hh h' hh' hm
    rcases Finset.mem_insert.1 hh with rfl | hh <;> rcases Finset.mem_insert.1 hh' with rfl | hh'
    · rfl
    · obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 hh'
      exact absurd hm (hone g' hg')
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hh
      exact absurd hm.symm (hone g hg)
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hh
      obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 hh'
      rw [hinj g hg g' hg' hm])
  rw [Finset.sum_insert hnot] at hbig
  have hq : (Nat.card (IsLocalRing.ResidueField O) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [Formalism.UG.P.tjcosets_card_residue]; rfl
  rw [hq] at hbig
  rw [hsum]
  change Φ 1 + ∑ h ∈ C.image (rho W π β), Φ h ≤ _ at hbig
  rw [hΦ1] at hbig
  rw [hσ] at hbig
  linarith

end GlobalTheory.SplitIndexSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumHeckeIndicatorIntegralEqPrimitive
section
noncomputable section

open Matrix GlobalTheory.SplitHecke GlobalTheory.ExportSeries

namespace GlobalTheory.HeckeMobius

section Pure

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K]

theorem reps_mul_central {n : ℕ} {ι : Type} {x c : GL (Fin n) K} {R : Finset ι} {ρ : ι → GL (Fin n) K}
    (hc : ∀ g : GL (Fin n) K, c * g = g * c) (h : Reps O x R ρ) :
    Reps O (x * c) R fun γ => ρ γ * c := by
  have hc' : ∀ g : GL (Fin n) K, c⁻¹ * g = g * c⁻¹ := fun g => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc g, mul_inv_cancel_right]
  refine ⟨fun γ hγ => ?_, fun k₁ k₂ h₁ h₂ => ?_⟩
  · obtain ⟨k₁, k₂, h₁, h₂, e⟩ := h.1 γ hγ
    exact ⟨k₁, k₂, h₁, h₂, by show ρ γ * c = _; rw [e]; simp only [mul_assoc, hc k₂]⟩
  · have e : ∀ γ, (ρ γ * c)⁻¹ * (k₁ * (x * c) * k₂) = (ρ γ)⁻¹ * (k₁ * x * k₂) := fun γ => by
      calc (ρ γ * c)⁻¹ * (k₁ * (x * c) * k₂) = c⁻¹ * ((ρ γ)⁻¹ * (k₁ * x * k₂)) * c := by
            rw [_root_.mul_inv_rev]; simp only [mul_assoc, hc k₂]
        _ = (ρ γ)⁻¹ * (k₁ * x * k₂) := by rw [hc', inv_mul_cancel_right]
    exact (existsUnique_congr fun γ => and_congr_right fun _ => by rw [e γ]).2 (h.2 k₁ k₂ h₁ h₂)

def scal {n : ℕ} (a : K) (ha : a ≠ 0) : GL (Fin n) K :=
  Units.map (Matrix.scalar (Fin n) : K →+* Matrix (Fin n) (Fin n) K).toMonoidHom (Units.mk0 a ha)

theorem scal_val {n : ℕ} (a : K) (ha : a ≠ 0) :
    ((scal a ha : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) a := rfl

theorem scal_comm {n : ℕ} (a : K) (ha : a ≠ 0) (g : GL (Fin n) K) : scal a ha * g = g * scal a ha :=
  Units.ext (by
    rw [Units.val_mul, Units.val_mul, scal_val]
    exact (Matrix.scalar_commute a (fun _ => Commute.all _ _) _).eq)

theorem scal_inv_comm {n : ℕ} (a : K) (ha : a ≠ 0) (g : GL (Fin n) K) : (scal a ha)⁻¹ * g = g * (scal a ha)⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, scal_comm, mul_inv_cancel_right]

theorem scal_mul_val {n : ℕ} (a : K) (ha : a ≠ 0) (g : GL (Fin n) K) : (scal a ha * g).1 = a • g.1 := by
  rw [Units.val_mul, scal_val, Matrix.scalar_apply, smul_eq_diagonal_mul]

theorem hk_compl {p : O} (hp : algebraMap O K p ≠ 0) {n j : ℕ} (hj : j ≤ n) {α : GL (Fin n) K} (h : Hk O p j α) :
    Hk O p (n - j) (scal (algebraMap O K p) hp * α⁻¹) := by
  refine ⟨by rw [scal_mul_val]; exact h.2.1, ?_, ?_⟩
  · have : algebraMap O K p • ((scal (algebraMap O K p) hp * α⁻¹)⁻¹ : GL (Fin n) K).1 = α.1 := by
      rw [← scal_mul_val _ hp, _root_.mul_inv_rev, inv_inv, ← mul_assoc, scal_comm, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact h.1
  · obtain ⟨u, hu⟩ := h.2.2
    refine ⟨u⁻¹, ?_⟩
    have h1 : (α⁻¹).1.det * α.1.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have h2 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [scal_mul_val, Matrix.det_smul, Fintype.card_fin, map_mul, map_pow]
    rw [hu, map_mul, map_pow] at h1
    have hn : algebraMap O K p ^ n = algebraMap O K p ^ (n - j) * algebraMap O K p ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    rw [hn]
    linear_combination (-(algebraMap O K p ^ (n - j) * algebraMap O K p ^ j * (α⁻¹).1.det)) * h2 +
      (algebraMap O K p ^ (n - j) * algebraMap O K ((u⁻¹ : Oˣ) : O)) * h1

theorem cond_eq {p : O} (hp : algebraMap O K p ≠ 0) {r n : ℕ} (g : GL (Fin r) K) (z : Matrix (Fin r) (Fin n) O) :
    ((algebraMap O K p)⁻¹ • zᵀ.map (algebraMap O K)) * (tr ((g * (scal (algebraMap O K p) hp)⁻¹)⁻¹)).1 =
      ((g⁻¹).1 * z.map (algebraMap O K))ᵀ := by
  have : (tr ((g * (scal (algebraMap O K p) hp)⁻¹)⁻¹)).1 = (algebraMap O K p • (g⁻¹).1)ᵀ := by
    rw [_root_.mul_inv_rev, inv_inv, ← scal_mul_val _ hp]; rfl
  rw [this, Matrix.transpose_mul, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ hp, one_smul]
  rfl


open IsLocalRing in
theorem count_eq [Finite (ResidueField O)] {p : O} (hp : Irreducible p) {r n k : ℕ} (hk : k ≤ r) {ι : Type}
    {α : GL (Fin r) K} {R : Finset ι} {ρ : ι → GL (Fin r) K} (hα : Hk O p k α) (hR : Reps O α R ρ)
    (z : Matrix (Fin r) (Fin n) O) :
    Nat.card {γ : ι // γ ∈ R ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))} =
      Nat.card {W : Submodule (ResidueField O)
        (Fin (Module.finrank (ResidueField O) (LinearMap.ker (z.map (residue O))ᵀ.mulVecLin)) → ResidueField O) //
          Module.finrank (ResidueField O) W = k} := by
  have h0 : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hp.ne_zero
  have hR' : Reps O (tr (scal (algebraMap O K p) h0 * α⁻¹)) R
      fun γ => tr ((ρ γ * (scal (algebraMap O K p) h0)⁻¹)⁻¹) := by
    apply Reps.tr
    rw [_root_.mul_inv_rev, inv_inv]
    exact reps_mul_central (scal_inv_comm _ h0) hR
  have hc := Cosets.card_cosets O K p hp n r (r - k) ι _ R _ zᵀ (Nat.sub_le r k) (hk_compl h0 hk hα).tr hR'
  calc Nat.card {γ : ι // γ ∈ R ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))}
      = Nat.card {γ : ι // γ ∈ R ∧ IntM O (((algebraMap O K p)⁻¹ • zᵀ.map (algebraMap O K)) *
          (tr ((ρ γ * (scal (algebraMap O K p) h0)⁻¹)⁻¹)).1)} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun γ => and_congr_right fun _ => by
          rw [cond_eq h0]; exact ⟨fun h => h.transpose, fun h => h.transpose⟩)
    _ = _ := hc
    _ = Nat.card {W : Submodule (ResidueField O) (Fin r → ResidueField O) //
          W ≤ LinearMap.ker (z.map (residue O))ᵀ.mulVecLin ∧ Module.finrank (ResidueField O) W = k} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun W => by
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
          · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩)
    _ = _ := GlobalTheory.card_subspaces_le_eq _ _
    _ = _ := GlobalTheory.card_subspaces_finrank_congr (LinearEquiv.ofFinrankEq _ _ (Module.finrank_fin_fun _).symm) k

theorem sum_smul_row {F : Type} [Field F] {r n : ℕ} (y : Matrix (Fin r) (Fin n) F) (g : Fin r → F) :
    yᵀ *ᵥ g = ∑ i, g i • y.row i := by
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.row, mul_comm]

end Pure


open IsLocalRing in
theorem sum_hecke_indicator_eq_prim : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Finite (IsLocalRing.ResidueField O)] (p : O), Irreducible p → ∀ (r n : ℕ) (ι : Type) (α : ℕ → GL (Fin r) K) (R : ℕ → Finset ι) (ρ : ι → GL (Fin r) K), (∀ k ∈ Finset.Icc 1 r, Hk O p k (α k) ∧ Reps O (α k) (R k) ρ) → ∀ z : Matrix (Fin r) (Fin n) O, (1 : ℂ) + ∑ k ∈ Finset.Icc 1 r, (-1 : ℂ) ^ k * (Nat.card (IsLocalRing.ResidueField O) : ℂ) ^ (k * (k - 1) / 2) * (Nat.card {γ : ι // γ ∈ R k ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))} : ℂ) = ((prim (z.map (IsLocalRing.residue O)) : ℚ) : ℂ) := by
  intro O K _ _ _ _ _ _ _ p hp r n ι α R ρ h z
  set A := (z.map (residue O))ᵀ with hA
  set c := Module.finrank (ResidueField O) (LinearMap.ker A.mulVecLin) with hc
  have hcr : c ≤ r := by
    have := Submodule.finrank_le (LinearMap.ker A.mulVecLin)
    rwa [Module.finrank_fin_fun] at this
  let N : ℕ → ℂ := fun k => (Nat.card {W : Submodule (ResidueField O) (Fin c → ResidueField O) //
    Module.finrank (ResidueField O) W = k} : ℂ)
  have hN0 : N 0 = 1 := by
    simp only [N, Submodule.finrank_eq_zero]
    rw [Nat.card_unique, Nat.cast_one]
  have hNc : ∀ k, c < k → N k = 0 := fun k hk => by
    simp only [N, Nat.cast_eq_zero]
    haveI : IsEmpty {W : Submodule (ResidueField O) (Fin c → ResidueField O) //
        Module.finrank (ResidueField O) W = k} := ⟨fun W => by
      have := Submodule.finrank_le W.1
      rw [Module.finrank_fin_fun, W.2] at this
      omega⟩
    exact Nat.card_of_isEmpty
  have e1 : (1 : ℂ) + ∑ k ∈ Finset.Icc 1 r, (-1 : ℂ) ^ k * (Nat.card (ResidueField O) : ℂ) ^ (k * (k - 1) / 2) *
      (Nat.card {γ : ι // γ ∈ R k ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))} : ℂ) =
      ∑ k ∈ Finset.range (r + 1), (-1 : ℂ) ^ k * (Nat.card (ResidueField O) : ℂ) ^ (k * (k - 1) / 2) * N k * 1 ^ k := by
    rw [Finset.sum_range_succ', pow_zero, pow_zero, one_mul, hN0, mul_one, one_mul, add_comm]
    congr 1
    have hI : Finset.Icc 1 r = Finset.Ico 1 (r + 1) := by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hI, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : 1 + k ≤ r := by rw [Finset.mem_range] at hk; omega
    have hm : 1 + k ∈ Finset.Icc 1 r := Finset.mem_Icc.2 ⟨by omega, hk'⟩
    rw [count_eq hp hk' (h _ hm).1 (h _ hm).2 z, one_pow, mul_one, add_comm 1 k]
  have hli : LinearIndependent (ResidueField O) (z.map (residue O)).row ↔ c = 0 := by
    rw [hc, Submodule.finrank_eq_zero, LinearMap.ker_eq_bot', Fintype.linearIndependent_iff]
    refine forall_congr' fun g => ?_
    rw [Matrix.mulVecLin_apply, hA, sum_smul_row]
    constructor
    · intro H h0; funext i; exact H h0 i
    · intro H h0 i; rw [H h0]; rfl
  rw [e1, ← Finset.sum_subset (Finset.range_subset_range.2 (show c + 1 ≤ r + 1 by omega)) (fun k hk hk' => ?_)]
  · refine Eq.trans (GlobalTheory.GaussSubspace.sum_card_subspaces (ResidueField O) c ℂ 1) ?_
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [prim, if_pos (hli.2 h0), h0, Finset.prod_range_zero]
      simp
    · rw [prim, if_neg (fun H => by have := hli.1 H; omega)]
      obtain ⟨m, hm⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
      rw [hm, Finset.prod_range_succ', pow_zero, one_mul, sub_self, mul_zero]
      simp
  · rw [Finset.mem_range, not_lt] at hk'
    rw [hNc k (by omega)]
    ring

end GlobalTheory.HeckeMobius
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialLevelCosetRepresentativeMemLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Eu

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


open Classical in
def fid (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : AE D :=
  if h : ∃ f, IsFinIdem D v f then h.choose else 0

def locSet (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) : Set (GA D (Wc D i)) :=
  {g | g ∈ GfC (Wc D i) ∧ SuppF (Wc D i) (fid D v) g}

def LX (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) : Type :=
  Quotient ((QuotientGroup.leftRel (levW R i)).comap (Subtype.val : locSet R i v → GA D (Wc D i)))

theorem one_mem_locSet (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (1 : GA D (Wc D i)) ∈ locSet R i v := by
  refine ⟨(GfC (Wc D i)).one_mem, ?_⟩
  have : Formalism.L2.Theta.mt (Wc D i) 1 = 1 := rfl
  intro a b
  simp [this]

def lx0 (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) : LX R i v :=
  Quotient.mk _ ⟨1, one_mem_locSet R i v⟩

def rep {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) : GA D (Wc D i) :=
  (Quotient.out x).1


open Classical in
def Bop (R : RealDat D A Ks) (i : Fin D.R.m) (γ : GA D (Wc D i)) :
    (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H :=
  if h : ∃ B : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H, ‖B‖ ≤ 1 ∧ ∀ x y, trPair R i γ x y = ⟪x, B y⟫_ℂ then
    h.choose else 0


open Classical in
def famProd (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v) : GA D (Wc D i) :=
  if h : {w | F w ≠ lx0 R i w}.Finite then (h.toFinset.toList.map fun w => rep (F w)).prod else 1

def Bfam (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, LX R i v) :
    (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H :=
  Bop R i (famProd R i F)

def acoef (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : LX R i v) : ℂ :=
  coef R i t μ 𝓕 (rep x)

def Zop (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H :=
  ∑' x : LX R i v, acoef R i t μ 𝓕 v x • Bop R i (rep x)

section Helpers
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem bop_one {R : RealDat D A Ks} {i : Fin D.R.m} (hTL : TransLaws R i) : Eu.Bop R i 1 = 1 := by
  have h6 : ∀ x y, trPair R i 1 x y = ⟪x, y⟫_ℂ := hTL.2.2.2.2.2
  have hex : ∃ B : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H, ‖B‖ ≤ 1 ∧
      ∀ x y, trPair R i 1 x y = ⟪x, B y⟫_ℂ :=
    ⟨1, ContinuousLinearMap.norm_id_le, fun x y => by rw [h6]; rfl⟩
  unfold Eu.Bop
  rw [dite_eq_left hex]
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [← hex.choose_spec.2 x y, h6]
  rfl

theorem bop_norm (R : RealDat D A Ks) (i : Fin D.R.m) (γ : GA D (Wc D i)) : ‖Eu.Bop R i γ‖ ≤ 1 := by
  unfold Eu.Bop
  split_ifs with h
  · exact h.choose_spec.1
  · simp

theorem trivial_level_coset_representative_mem_level (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Eu.rep (Eu.lx0 R i v) ∈ levW R i := by
  have h := Quotient.mk_out (s := (QuotientGroup.leftRel (levW R i)).comap
    (Subtype.val : Eu.locSet R i v → GA D (Wc D i))) ⟨1, Eu.one_mem_locSet R i v⟩
  rw [Setoid.comap_rel, QuotientGroup.leftRel_apply] at h
  have h2 := h
  have h3 := (levW R i).inv_mem h2
  simpa [Eu.rep, Eu.lx0] using h3

theorem local_coefficient_trivial_level_coset {R : RealDat D A Ks} {i : Fin D.R.m} {t : T} (hLF : LevFix R i t) (hVN : VecNe R i t) {μ 𝓕}
    (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Eu.acoef R i t μ 𝓕 v (Eu.lx0 R i v) = 1 := by
  unfold Eu.acoef
  have := Model.coef_mul_lev R i t hLF μ 𝓕 1 _ (trivial_level_coset_representative_mem_level R i v)
  rw [one_mul] at this
  rw [this, Model.coef_one R i t hVN μ 𝓕 hμ]

theorem localCosetFamilyRepresentativeProd_trivial_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) : Eu.famProd R i (Eu.lx0 R i) = 1 := by
  unfold Eu.famProd
  have hf : {w | Eu.lx0 R i w ≠ Eu.lx0 R i w}.Finite := by simp
  rw [dite_eq_left hf]
  have : hf.toFinset = ∅ := by simp
  rw [this]
  simp

end Helpers

end GlobalTheory.RawLift.Eu

end
end

