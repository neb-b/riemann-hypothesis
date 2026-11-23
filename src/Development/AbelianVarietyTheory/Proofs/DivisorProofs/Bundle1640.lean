module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralUnitRootNormOneAdele
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0449
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicLeviNormOneLastColumnProdEquiv
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.LeviLast

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem cT_mul_sq {R : Type} [CommRing R] (s : R →+* R) {k : ℕ} (A B : Matrix (Fin k) (Fin k) R) :
    cT s (A * B) = cT s B * cT s A := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one_sq {R : Type} [CommRing R] (s : R →+* R) {k : ℕ} : cT s (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  simp only [Formalism.UG.cT, Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

def cTUnit {R : Type} [CommRing R] (s : R →+* R) {k : ℕ} (β : GL (Fin k) R) : GL (Fin k) R where
  val := cT s (β⁻¹).1
  inv := cT s β.1
  val_inv := by rw [← cT_mul_sq, Units.mul_inv, cT_one_sq]
  inv_val := by rw [← cT_mul_sq, Units.inv_mul, cT_one_sq]

theorem adMat_mul' {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    adMat F (A * B) = adMat F A * adMat F B := Matrix.map_mul

theorem adMat_one' {a : ℕ} : adMat F (1 : Matrix (Fin a) (Fin a) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

def blk {k : ℕ} (P : Matrix (Fin k) (Fin n) E) (X : Matrix (Fin n) (Fin k) E) (g : GAd σ J) :
    Matrix (Fin k) (Fin k) (AF F ⊗[F] E) :=
  adMat F P * (matHom _ σ J g).1 * adMat F X

theorem blk_of {k : ℕ} {P : Matrix (Fin k) (Fin n) E} {X : Matrix (Fin n) (Fin k) E} (hPX : P * X = 1) {g : GAd σ J}
    {B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)} (h : (matHom _ σ J g).1 * adMat F X = adMat F X * B) : blk P X g = B := by
  rw [blk, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← adMat_mul', hPX, adMat_one', Matrix.one_mul]

theorem blk_mul {k : ℕ} {P : Matrix (Fin k) (Fin n) E} {X : Matrix (Fin n) (Fin k) E} (hPX : P * X = 1) (a : GAd σ J)
    {b : GAd σ J} {B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)} (h : (matHom _ σ J b).1 * adMat F X = adMat F X * B) :
    blk P X (a * b) = blk P X a * blk P X b := by
  rw [blk_of hPX h, blk, blk, map_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]
  rw [h]

variable {r : ℕ}

theorem mem_leviOne_last {X Y : Matrix (Fin n) (Fin (r + 1)) E} {g : GAd σ J} :
    g ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ↔
      (∃ B : GL (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F X = adMat F X * B.1) ∧
      (∃ B : GL (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F Y = adMat F Y * B.1) ∧
      (∃ B ∈ ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker,
        (matHom _ σ J g).1 * adMat F X = adMat F X * B.1) := by
  have hmem : g ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ↔ ∀ k ∈ ({Fin.last r} : Finset (Fin (r + 1))),
      g ∈ GlobalTheory.StdPar.frameStab σ J (GlobalTheory.StdPar.initCols X k) ((⊤ : Subgroup (AF F ⊗[F] E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ GlobalTheory.StdPar.frameStab σ J (GlobalTheory.StdPar.initCols Y k) ((⊤ : Subgroup (AF F ⊗[F] E)ˣ).comap Matrix.GeneralLinearGroup.det) ∧
      g ∈ GlobalTheory.StdPar.frameStab σ J (GlobalTheory.StdPar.initCols X k) ((absE F E).ker.comap Matrix.GeneralLinearGroup.det) := by
    simp only [GlobalTheory.StdPar.leviOne, GlobalTheory.StdPar.levi, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.comap_top, MonoidHom.comap_ker]
    exact ⟨fun h k hk => ⟨(h.1 k hk).1, (h.1 k hk).2, h.2 k hk⟩, fun h => ⟨fun k hk => ⟨(h k hk).1, (h k hk).2.1⟩, fun k hk => (h k hk).2.2⟩⟩
  rw [hmem]
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · rintro ⟨⟨B, -, h⟩, ⟨B', -, h'⟩, ⟨B'', h2, h''⟩⟩
    exact ⟨⟨B, h⟩, ⟨B', h'⟩, ⟨B'', h2, h''⟩⟩
  · rintro ⟨⟨B, h⟩, ⟨B', h'⟩, ⟨B'', h2, h''⟩⟩
    exact ⟨⟨B, Subgroup.mem_top _, h⟩, ⟨B', Subgroup.mem_top _, h'⟩, ⟨B'', h2, h''⟩⟩


set_option maxHeartbeats 1000000 in
open GlobalTheory.UAut GlobalTheory.EisLine in
theorem leviOne_last_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∃ φ : (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) × ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ≃ₜ* GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∀ p, ((φ p : GAd σ J) ∈ ratPts σ J ↔ (p.1 : GAd σ J) ∈ ratPts σ J ∧ (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)) ∈ (bc (inclR (F := F) (AF F)) : GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range) := by
  intro F E _ _ _ _ _ σ n J r m X Y Z J₀ hF
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  obtain ⟨lv, hlv, -, -⟩ := GlobalTheory.SphEis.Inhabitant.existsUnique_isLv hF
  set K := ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker with hK
  set A := GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} with hA
  set T := (GlobalTheory.SphEis.fixG σ J X ⊓ GlobalTheory.SphEis.fixG σ J Y : Subgroup (GAd σ J)) with hT
  set P : Matrix (Fin (r + 1)) (Fin n) E := cT (σ : E →+* E) Y * J with hP
  set Q : Matrix (Fin (r + 1)) (Fin n) E := cT (σ : E →+* E) X * J with hQ
  have hPX : P * X = 1 := hF.dc
  have hQY : Q * Y = 1 := hF.cd
  have h1X : ∀ g : GAd σ J, (matHom _ σ J g).1 * adMat F X = adMat F X →
      (matHom _ σ J g).1 * adMat F X = adMat F X * (1 : GL (Fin (r + 1)) (AF F ⊗[F] E)).1 := fun g h => by
    rw [Units.val_one, Matrix.mul_one]; exact h
  have hinv : ∀ a : A, blk P X (a : GAd σ J) * blk P X ((a⁻¹ : A) : GAd σ J) = 1 ∧
      blk P X ((a⁻¹ : A) : GAd σ J) * blk P X (a : GAd σ J) = 1 := by
    intro a
    obtain ⟨⟨B, hB⟩, -, -⟩ := mem_leviOne_last.1 a.2
    obtain ⟨⟨B', hB'⟩, -, -⟩ := mem_leviOne_last.1 (a⁻¹).2
    have e1 : blk P X (1 : GAd σ J) = 1 := by
      have := blk_of hPX (h1X 1 (by rw [map_one, Units.val_one, Matrix.one_mul]))
      rw [this, Units.val_one]
    refine ⟨?_, ?_⟩
    · rw [← blk_mul hPX _ hB', ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, e1]
    · rw [← blk_mul hPX _ hB, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, e1]
  let πu : A → GL (Fin (r + 1)) (AF F ⊗[F] E) := fun a =>
    ⟨blk P X (a : GAd σ J), blk P X ((a⁻¹ : A) : GAd σ J), (hinv a).1, (hinv a).2⟩
  have hπK : ∀ a : A, πu a ∈ K := by
    intro a
    obtain ⟨-, -, ⟨B, hBK, hB⟩⟩ := mem_leviOne_last.1 a.2
    have : πu a = B := Units.ext (blk_of hPX hB)
    rw [this]; exact hBK
  let π : A → K := fun a => ⟨πu a, hπK a⟩
  have hlvA : ∀ β : K, lv β ∈ A := fun β =>
    mem_leviOne_last.2 ⟨⟨β, hlv.onC β⟩, ⟨cTUnit (sigR (AF F) σ) (β : GL (Fin (r + 1)) (AF F ⊗[F] E)), hlv.onD β⟩,
      ⟨β, β.2, hlv.onC β⟩⟩
  let mm : K → A := fun β => ⟨lv β, hlvA β⟩
  have hTA : T ≤ A := by
    intro x hx
    obtain ⟨hxX, hxY⟩ := Subgroup.mem_inf.1 hx
    have hX' : (matHom _ σ J x).1 * adMat F X = adMat F X := hxX
    have hY' : (matHom _ σ J x).1 * adMat F Y = adMat F Y := hxY
    exact mem_leviOne_last.2 ⟨⟨1, by rw [hX', Units.val_one, Matrix.mul_one]⟩, ⟨1, by rw [hY', Units.val_one, Matrix.mul_one]⟩,
      ⟨1, one_mem _, by rw [hX', Units.val_one, Matrix.mul_one]⟩⟩
  have hTiff : ∀ a : A, (a : GAd σ J) ∈ T ↔ π a = 1 := by
    intro a
    constructor
    · intro hx
      exact Subtype.ext (Units.ext (blk_of hPX (h1X _ (Subgroup.mem_inf.1 hx).1)))
    · intro h1
      have hb : blk P X (a : GAd σ J) = 1 := by
        have := congrArg (fun x : K => (x : GL (Fin (r + 1)) (AF F ⊗[F] E)).1) h1
        exact this
      obtain ⟨⟨B, hB⟩, ⟨B', hB'⟩, -⟩ := mem_leviOne_last.1 a.2
      have hB1 : B.1 = 1 := (blk_of hPX hB).symm.trans hb
      have hfX : (matHom _ σ J (a : GAd σ J)).1 * adMat F X = adMat F X := by rw [hB, hB1, Matrix.mul_one]
      have hfXi : (a : GAd σ J)⁻¹ ∈ GlobalTheory.SphEis.fixG σ J X :=
        inv_mem (show (a : GAd σ J) ∈ GlobalTheory.SphEis.fixG σ J X from hfX)
      have hform := form_mul_of_mul_cols (B := 1)
        (show (matHom _ σ J (a : GAd σ J)⁻¹).1 * adMat F X = adMat F X * 1 by rw [Matrix.mul_one]; exact hfXi)
      rw [inv_inv, cT_one_sq, Matrix.one_mul] at hform
      have e1 : blk Q Y (a : GAd σ J) = B'.1 := blk_of hQY hB'
      rw [blk, hform, ← adMat_mul', hQY, adMat_one'] at e1
      have hfY : (matHom _ σ J (a : GAd σ J)).1 * adMat F Y = adMat F Y := by rw [hB', ← e1, Matrix.mul_one]
      exact Subgroup.mem_inf.2 ⟨hfX, hfY⟩
  have hπc : Continuous π := by
    refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun a : A => adMat F P * (matHom _ σ J (a : GAd σ J)).1 * adMat F X
      exact (continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.comp continuous_subtype_val)).matrix_mul continuous_const
    · show Continuous fun a : A => adMat F P * (matHom _ σ J ((a⁻¹ : A) : GAd σ J)).1 * adMat F X
      exact (continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.comp (continuous_subtype_val.comp continuous_inv))).matrix_mul
        continuous_const
  have hmc : Continuous mm := (hlv.cont.comp continuous_subtype_val).subtype_mk _
  have hmm : ∀ a b, mm (a * b) = mm a * mm b := fun a b => Subtype.ext (map_mul lv _ _)
  have hππ : ∀ a b, π (a * b) = π a * π b := by
    intro a b
    obtain ⟨⟨B, hB⟩, -, -⟩ := mem_leviOne_last.1 b.2
    exact Subtype.ext (Units.ext (blk_mul hPX (a : GAd σ J) hB))
  have hπm : ∀ β, π (mm β) = β := fun β => Subtype.ext (Units.ext (blk_of hPX (hlv.onC β)))
  have hc : ∀ τ ∈ T, ∀ β, τ * (mm β : GAd σ J) = mm β * τ := fun τ hτ β =>
    (GlobalTheory.SphEis.lv_comm_of_fix_cols F E σ n J (r + 1) m X Y Z J₀ hF lv hlv β τ hτ).symm
  obtain ⟨φ, hφ⟩ := GlobalTheory.LeviSplit.exists_prod_equiv A T mm π hmc hπc hmm hππ hπm hTA hTiff hc
  refine ⟨φ, fun p => ?_⟩
  rw [hφ p]
  change (p.1 : GAd σ J) * lv p.2 ∈ ratPts σ J ↔ _
  constructor
  · intro h
    have hp1 : (matHom _ σ J (p.1 : GAd σ J)).1 * adMat F X = adMat F X := (Subgroup.mem_inf.1 p.1.2).1
    have hg : (matHom _ σ J ((p.1 : GAd σ J) * lv p.2)).1 * adMat F X =
        adMat F X * (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)).1 := by
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, hlv.onC, ← Matrix.mul_assoc, hp1]
    have hb := blk_of hPX hg
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h)
    have hM : (matHom _ σ J ((p.1 : GAd σ J) * lv p.2)).1 = adMat F γ.1 := (congrArg Units.val hγ).symm
    rw [blk, hM, ← adMat_mul', ← adMat_mul'] at hb
    have hrng : (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)) ∈ (bc (inclR (F := F) (AF F)) :
        GL (Fin (r + 1)) E →* GL (Fin (r + 1)) (AF F ⊗[F] E)).range := by
      rcases subsingleton_or_nontrivial (AF F ⊗[F] E) with _ | _
      · exact ⟨1, Units.ext (Subsingleton.elim _ _)⟩
      · have hd : (P * γ.1 * X).det ≠ 0 := fun h0 => by
          have hu : IsUnit (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)).1.det :=
            (Matrix.isUnit_iff_isUnit_det _).1 (p.2 : GL (Fin (r + 1)) (AF F ⊗[F] E)).isUnit
          rw [← hb, show (adMat F (P * γ.1 * X)).det = inclR (F := F) (AF F) (P * γ.1 * X).det from
            (RingHom.map_det _ _).symm, h0, map_zero] at hu
          exact not_isUnit_zero hu
        exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, Units.ext hb⟩
    obtain ⟨δ, hδ⟩ := hrng
    refine ⟨?_, ⟨δ, hδ⟩⟩
    have h2 : lv p.2 ∈ ratPts σ J := by rw [← hδ]; exact hlv.rat δ
    have := mul_mem h (inv_mem h2)
    rwa [mul_inv_cancel_right] at this
  · rintro ⟨h1, ⟨δ, hδ⟩⟩
    refine mul_mem h1 ?_
    rw [← hδ]; exact hlv.rat δ

end GlobalTheory.SphEis.LeviLast
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableSchwartzSeries
section
open Filter
open scoped SchwartzMap Topology

namespace GlobalTheory
namespace SchwartzSum

theorem hasSum_of_summable_seminorms :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {ι : Type}
    (u : ι → SchwartzMap V ℂ), (∀ k n : ℕ, Summable (fun i => SchwartzMap.seminorm ℂ k n (u i))) →
    ∃ F : SchwartzMap V ℂ, (∀ x, HasSum (fun i => u i x) (F x)) ∧
      ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, HasSum (fun i => T (u i)) (T F) := by
  intro V _ _ _ ι u hu
  have iteratedFDeriv_sub' (f g : 𝓢(V, ℂ)) (n : ℕ) (x : V) :
      iteratedFDeriv ℝ n (⇑(f - g)) x = iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n g x := by
    have hf : ContDiff ℝ n f := f.smooth n
    have hg : ContDiff ℝ n g := g.smooth n
    rw [show (⇑(f - g) : V → ℂ) = ⇑f - ⇑g from rfl]
    exact iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt

  have cauchy_seminorm {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
      ∃ N, ∀ a ≥ N, ∀ b ≥ N, SchwartzMap.seminorm ℝ k n (u a - u b) < ε := by
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff] at hu
    have h := ((schwartz_withSeminorms ℝ V ℂ).tendsto_nhds _ 0).1 hu (k, n) ε hε
    obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h
    refine ⟨max N₁ N₂, fun a ha b hb => ?_⟩
    have := hN (b, a) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hb, le_of_max_le_right ha⟩)
    simpa [schwartzSeminormFamily] using this

  let limD (u : ℕ → 𝓢(V, ℂ)) (n : ℕ) (x : V) :
      ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℂ :=
    limUnder atTop fun j => iteratedFDeriv ℝ n (u j) x

  have tendsto_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) (x : V) :
      Tendsto (fun j => iteratedFDeriv ℝ n (u j) x) atTop (𝓝 (limD u n x)) := by
    refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := cauchy_seminorm hu 0 n hε
    refine ⟨N, fun a ha b hb => ?_⟩
    rw [dist_eq_norm, ← iteratedFDeriv_sub']
    have := SchwartzMap.le_seminorm ℝ 0 n (u a - u b) x
    simp only [pow_zero, one_mul] at this
    exact this.trans_lt (hN a ha b hb)

  have key {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
      ∃ N, ∀ j ≥ N, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖ ≤ ε := by
    obtain ⟨N, hN⟩ := cauchy_seminorm hu k n hε
    refine ⟨N, fun j hj x => ?_⟩
    have ht : Tendsto (fun b => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - iteratedFDeriv ℝ n (u b) x‖)
        atTop (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖)) :=
      ((tendsto_const_nhds.sub (tendsto_limD hu n x)).norm).const_mul _
    refine le_of_tendsto ht (eventually_atTop.2 ⟨N, fun b hb => ?_⟩)
    rw [← iteratedFDeriv_sub']
    exact (SchwartzMap.le_seminorm ℝ k n (u j - u b) x).trans (hN j hj b hb).le

  have tendstoUniformly_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) :
      TendstoUniformly (fun j => iteratedFDeriv ℝ n (u j)) (limD u n) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := key hu 0 n (half_pos hε)
    refine eventually_atTop.2 ⟨N, fun j hj x => ?_⟩
    have := hN j hj x
    rw [pow_zero, one_mul] at this
    rw [dist_eq_norm, norm_sub_rev]
    linarith

  have continuous_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) :
      Continuous (limD u n) :=
    (tendstoUniformly_limD hu n).continuous (Eventually.of_forall (f := atTop) fun j =>
      ((u j).smooth ⊤).continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).frequently

  have hasFDerivAt_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (m : ℕ) (x : V) :
      HasFDerivAt (limD u m) ((limD u (m + 1) x).curryLeft) x := by
    refine hasFDerivAt_of_tendstoUniformly (f := fun j => iteratedFDeriv ℝ m (u j))
      (f' := fun j y => fderiv ℝ (iteratedFDeriv ℝ m (u j)) y)
      (g' := fun y => (limD u (m + 1) y).curryLeft) ?_ ?_ (fun y => tendsto_limD hu m y) x
    · exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) ℂ).isometry.uniformContinuous.comp_tendstoUniformly
        (tendstoUniformly_limD hu (m + 1))
    · intro j y
      exact ((((u j).smooth ⊤).differentiable_iteratedFDeriv
        (by exact_mod_cast WithTop.coe_lt_top (m : ℕ))) y).hasFDerivAt

  have hasFTaylorSeries {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) :
      HasFTaylorSeriesUpTo ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (limD u 0 x).curry0)
        (fun x => (fun m => limD u m x : FormalMultilinearSeries ℝ V ℂ)) :=
    { zero_eq := fun _ => rfl
      fderiv := fun m _ x => hasFDerivAt_limD hu m x
      cont := fun m _ => continuous_limD hu m }

  let limMap (u : ℕ → 𝓢(V, ℂ)) (hu : CauchySeq u) : 𝓢(V, ℂ) := {
    toFun x := (limD u 0 x).curry0
    smooth' := (hasFTaylorSeries hu).contDiff
    decay' k n := by
      obtain ⟨N, hN⟩ := key hu k n one_pos
      refine ⟨SchwartzMap.seminorm ℝ k n (u N) + 1, fun x => ?_⟩
      rw [← (hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x]
      have h1 := hN N le_rfl x
      have h2 := SchwartzMap.le_seminorm ℝ k n (u N) x
      have h3 : ‖limD u n x‖ ≤ ‖iteratedFDeriv ℝ n (u N) x‖ + ‖iteratedFDeriv ℝ n (u N) x - limD u n x‖ := by
        have := norm_sub_le (iteratedFDeriv ℝ n (u N) x) (iteratedFDeriv ℝ n (u N) x - limD u n x)
        simpa using this
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ ‖x‖ ^ k)
      change ‖x‖ ^ k * ‖limD u n x‖ ≤ _
      rw [mul_add] at h4
      linarith }

  have iteratedFDeriv_limMap {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) (x : V) :
      iteratedFDeriv ℝ n (limMap u hu) x = limD u n x :=
    ((hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x).symm

  have tendsto_limMap {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) :
      Tendsto u atTop (𝓝 (limMap u hu)) := by
    rw [(schwartz_withSeminorms ℝ V ℂ).tendsto_nhds]
    rintro ⟨k, n⟩ ε hε
    obtain ⟨N, hN⟩ := key hu k n (half_pos hε)
    refine eventually_atTop.2 ⟨N, fun j hj => ?_⟩
    refine lt_of_le_of_lt ?_ (half_lt_self hε)
    refine SchwartzMap.seminorm_le_bound ℝ k n _ (half_pos hε).le fun x => ?_
    rw [iteratedFDeriv_sub', iteratedFDeriv_limMap hu]
    exact hN j hj x

  haveI : CompleteSpace 𝓢(V, ℂ) := by
    haveI : (uniformity 𝓢(V, ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
    exact UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ⟨limMap u hu, tendsto_limMap hu⟩

  have hS : Summable u := by
    rw [summable_iff_vanishing]
    intro e he
    obtain ⟨⟨S, r⟩, hr, hsub⟩ := (schwartz_withSeminorms ℂ V ℂ).hasBasis_zero_ball.mem_iff.1 he
    simp only at hr hsub
    have hg : Summable (fun i => ∑ kn ∈ S, schwartzSeminormFamily ℂ V ℂ kn (u i)) :=
      summable_sum fun kn _ => hu kn.1 kn.2
    obtain ⟨s, hs⟩ := (summable_iff_vanishing_norm.1 hg) r hr
    refine ⟨s, fun t ht => hsub ?_⟩
    rw [Seminorm.mem_ball_zero]
    have h1 := hs t ht
    calc (S.sup (schwartzSeminormFamily ℂ V ℂ)) (∑ i ∈ t, u i)
        ≤ ∑ kn ∈ S, schwartzSeminormFamily ℂ V ℂ kn (∑ i ∈ t, u i) :=
          Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => apply_nonneg _ _) fun kn hkn =>
            Finset.single_le_sum (f := fun kn => schwartzSeminormFamily ℂ V ℂ kn (∑ i ∈ t, u i))
              (fun _ _ => apply_nonneg _ _) hkn
      _ ≤ ∑ kn ∈ S, ∑ i ∈ t, schwartzSeminormFamily ℂ V ℂ kn (u i) :=
          Finset.sum_le_sum fun kn _ =>
            Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _
      _ = ∑ i ∈ t, ∑ kn ∈ S, schwartzSeminormFamily ℂ V ℂ kn (u i) := Finset.sum_comm
      _ ≤ ‖∑ i ∈ t, ∑ kn ∈ S, schwartzSeminormFamily ℂ V ℂ kn (u i)‖ := Real.le_norm_self _
      _ < r := h1
  refine ⟨∑' i, u i, fun x => ?_, fun T => hS.hasSum.mapL T⟩
  have h := hS.hasSum.mapL ((BoundedContinuousFunction.evalCLM ℂ x).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ))
  simpa using h

end SchwartzSum
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameOnBaseCharacter
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MuLift

section Ring

end Ring

section General

open NumberField Formalism.L2.DIV
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end General

section Adelic

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
open Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj GlobalTheory.StepLaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_idemSum (P : Finset (Pl D.host.E))
    (h : ∀ Q ∈ P, ∀ Q' ∈ P, ¬ Formalism.IndefR.Lev.IsConjPl Q Q') :
    ∃ e : AE D, IsIdemSum e P :=
  GlobalTheory.GridIdem.exists_isIdemSum P (fun Q hQ => GlobalTheory.ParahoricLift.exists_isIdemAt (h Q hQ Q hQ))
    fun Q hQ Q' hQ' e => (GlobalTheory.IdemSupport.eq_or_eq_cP e).resolve_right fun e' =>
      h Q' hQ' Q hQ ((GlobalTheory.IdemSupport.isConjPl_iff Q' Q).2 e')


end Adelic

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar


end GlobalTheory.MuLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModerateGrowthHeight
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace GlobalTheory.ThetaModGrowthPair

theorem theta_modGrowth : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  have hlat := _root_.GlobalTheory.LatScaleSum.thetaSum_norm_le_pow
  have hfin := _root_.GlobalTheory.FinSupp.exists_common_denominator
  have harch := _root_.GlobalTheory.ArchDecay.om_bound_arch
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨N₀, k₂, C₂, hL⟩ := hlat F (Fin n × Fin d)
  obtain ⟨C₁, k₁, hA⟩ := harch F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ N₀
  obtain ⟨C₃, k₃, hF⟩ := hfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  refine ⟨|C₂| * |C₁| * |C₃| ^ k₂, k₁ + k₃ * k₂, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hsupp⟩ := hF g h
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have hb := hL (C₁ * H ^ k₁) m (om (g, h) Φ) hm1 (fun ξ => hA g h _) hsupp
  have hA0 : 0 ≤ C₁ * H ^ k₁ :=
    le_trans (by positivity) (hA g h (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)))
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ k₂ := by positivity
  have hmk : (m : ℝ) ^ k₂ ≤ (|C₃| * H ^ k₃) ^ k₂ :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _))) _
  have hC1 : C₁ * H ^ k₁ ≤ |C₁| * H ^ k₁ := mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _)
  show ‖thetaSum F (om (g, h) Φ)‖ ≤ _
  calc ‖thetaSum F (om (g, h) Φ)‖ ≤ C₂ * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ := hb
    _ ≤ |C₂| * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hA0) hm0
    _ ≤ |C₂| * (|C₁| * H ^ k₁) * (|C₃| * H ^ k₃) ^ k₂ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hC1 (abs_nonneg _)) hmk hm0 (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (pow_nonneg hH0 _)))
    _ = |C₂| * |C₁| * |C₃| ^ k₂ * H ^ (k₁ + k₃ * k₂) := by rw [pow_add, pow_mul]; ring

end GlobalTheory.ThetaModGrowthPair
end

