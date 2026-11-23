module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixCongrAdelicMatrixModNat
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.CosetApprox

theorem exists_mem_approx (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (m : ℕ) (hm : 0 < m) (y : AE D)
    (hy : y ∈ hatId D 𝔪) : ∃ b ∈ 𝔪, ∃ t ∈ IhE D ⊤, inc D (b : D.host.E) - y = (m : AE D) * t := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hx
    obtain ⟨r, w, hw, e⟩ := GlobalTheory.AdelicApprox.exists_approx D m hm s hs
    have hr : inc D r ∈ OhE D := by
      have : inc D r = s - (m : AE D) * w := by rw [e]; ring
      rw [this]
      exact sub_mem hs (mul_mem (natCast_mem _ m) hw)
    have hri : IsIntegral ℤ r := Formalism.UG.P.csGlob_int (F := ℚ) _ hr
    let r' : 𝓞 D.host.E := ⟨r, hri⟩
    have hbr : b * r' ∈ 𝔪 := Ideal.mul_mem_right _ _ hb
    have hbw : inc D (b : D.host.E) * w ∈ OhE D := mul_mem (Formalism.UG.P.adelstab_incl_int b) hw
    refine ⟨b * r', hbr, -(inc D (b : D.host.E) * w), neg_mem ?_, ?_⟩
    · have := GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D ⊤ _ hbw
      simpa using this
    · have hc : ((b * r' : 𝓞 D.host.E) : D.host.E) = (b : D.host.E) * r := rfl
      rw [hc, map_mul, e]
      ring
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, t, ht, e⟩ := hx
    obtain ⟨b', hb', t', ht', e'⟩ := hy
    refine ⟨b + b', add_mem hb hb', t + t', add_mem ht ht', ?_⟩
    push_cast
    rw [map_add (f := _)]
    linear_combination e + e'
  | neg x _ hx =>
    obtain ⟨b, hb, t, ht, e⟩ := hx
    refine ⟨-b, neg_mem hb, -t, neg_mem ht, ?_⟩
    push_cast
    rw [map_neg]
    linear_combination -e

theorem matrix_approx : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (Y : Matrix (Fin d) (Fin a) (AE D)),
    (∀ i j, Y i j ∈ hatId D 𝔪) → ∀ m : ℕ, 0 < m → ∃ w : Matrix (Fin d) (Fin a) D.host.E,
      (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧ ∀ i j, ∃ y ∈ IhE D ⊤, (w.map (inc D) - Y) i j = (m : AE D) * y := by
  intro D 𝔪 a d Y hY m hm
  choose b hb t ht e using fun i j => exists_mem_approx D 𝔪 m hm (Y i j) (hY i j)
  refine ⟨Matrix.of fun i j => ((b i j : 𝓞 D.host.E) : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩,
    fun i j => ⟨t i j, ht i j, ?_⟩⟩
  simpa using e i j

end GlobalTheory.FunObj.CosetApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompactOfUnipotentCoordinatesMem
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem exists_isCompact_of_crd_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ Ω : Set (AF F ⊗[F] E), IsCompact Ω → ∃ V : Set (GAd σ J), IsCompact V ∧ ∀ (u : GAd σ J) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c → (∀ i k, b i k ∈ Ω) → (∀ i k, c i k ∈ Ω) → u ∈ V := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hFr Ω hΩ
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  let Φ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := fun p =>
    adMat F C * adMat F (cT (σ : E →+* E) D * J) + (adMat F Z + adMat F C * p.1) * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      (adMat F D - adMat F Z * plus σ J₀ p.1 + adMat F C * p.2) * adMat F (cT (σ : E →+* E) C * J)
  have key : ∀ u b c, Crd σ J C D Z J₀ u b c → (matHom _ σ J u).1 = Φ (b, c) := by
    intro u b c h
    have hs : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
        adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1 := by
      have := congrArg (Matrix.map · (inclR (F := F) (E := E) (AF F))) hFr.sum
      simpa only [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using this
    calc (matHom _ σ J u).1 = (matHom _ σ J u).1 * 1 := (Matrix.mul_one _).symm
      _ = Φ (b, c) := by
        rw [← hs, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc _ (adMat F C), ← Matrix.mul_assoc _ (adMat F Z),
          ← Matrix.mul_assoc _ (adMat F D), h.onC, h.onZ, h.onD]
  have hsig := GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ
  have hΦ : Continuous Φ := by
    have h1 : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => p.1 := continuous_fst
    have h2 : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => p.2 := continuous_snd
    have hp : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => plus σ J₀ p.1 :=
      continuous_const.matrix_mul (h1.matrix_map hsig).matrix_transpose
    exact ((continuous_const.add ((continuous_const.add (continuous_const.matrix_mul h1)).matrix_mul continuous_const)).add
      (((continuous_const.sub (continuous_const.matrix_mul hp)).add (continuous_const.matrix_mul h2)).matrix_mul continuous_const))
  have hadj : Continuous (adjA σ J) := by
    have : Continuous fun X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) => cT (sigR (AF F) σ) X :=
      (continuous_id.matrix_map hsig).matrix_transpose
    exact (continuous_const.matrix_mul this).matrix_mul continuous_const
  let S : Set (Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :=
    (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω) ×ˢ (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω)
  have hS : IsCompact S := (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ).prod
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ)
  let ψ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) × (Matrix (Fin n) (Fin n) (AF F ⊗[F] E))ᵐᵒᵖ :=
    fun p => (Φ p, MulOpposite.op (adjA σ J (Φ p)))
  have hψ : Continuous ψ := hΦ.prodMk (MulOpposite.continuous_op.comp (hadj.comp hΦ))
  have hce : IsClosedEmbedding fun g : GAd σ J => Units.embedProduct _ (matHom _ σ J g) :=
    (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).comp (isClosedEmbedding_matHom_GAd σ J)
  refine ⟨(fun g : GAd σ J => Units.embedProduct _ (matHom _ σ J g)) ⁻¹' (ψ '' S), hce.isCompact_preimage (hS.image hψ), ?_⟩
  intro u b c h hb hc
  refine ⟨(b, c), ⟨fun i _ k _ => hb i k, fun i _ k _ => hc i k⟩, ?_⟩
  have e1 := key u b c h
  have e2 := adjA_mat hFr.herm u
  simp only [ψ, Units.embedProduct_apply, ← e1, e2, ← map_inv]

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviCentreFlowWittFrame
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResidueFlow

open Matrix GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (conjUnit)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem row_of_stab {X Y : Matrix (Fin n) (Fin r) E} (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {g : GAd σ J} {B C : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}
    (hX : (matHom _ σ J g).1 * adMat F X = adMat F X * B) (hY : (matHom _ σ J g⁻¹).1 * adMat F Y = adMat F Y * C) :
    adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 = B * adMat F (cT (σ : E →+* E) Y * J) := by
  set S := sigR (AF F) σ with hS
  set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g).1 with hMdef
  set Mi : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g⁻¹).1 with hMidef
  have hinv : matHom (AF F) σ J g⁻¹ = (matHom (AF F) σ J g)⁻¹ := map_inv _ g
  have hMMi : M * Mi = 1 := by
    rw [hMdef, hMidef, hinv]; exact Units.mul_inv _
  have hU : cT S M * adMat F J * M = adMat F J := g.2
  have hadY : adMat F (cT (σ : E →+* E) Y * J) = cT S (adMat F Y) * adMat F J := by
    rw [adMat, Matrix.map_mul]
    congr 1
  have hJM : adMat F J * M = cT S Mi * adMat F J := by
    calc adMat F J * M = (cT S Mi * cT S M) * adMat F J * M := by
          rw [← Formalism.UG.cT_mul, hMMi, Formalism.UG.cT_one, Matrix.one_mul]
      _ = cT S Mi * (cT S M * adMat F J * M) := by simp only [Matrix.mul_assoc]
      _ = cT S Mi * adMat F J := by rw [hU]
  have h1 : adMat F (cT (σ : E →+* E) Y * J) * M = cT S C * adMat F (cT (σ : E →+* E) Y * J) := by
    rw [hadY, Matrix.mul_assoc, hJM, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hY, Formalism.UG.cT_mul, Matrix.mul_assoc]
  have hyx : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, GlobalTheory.StdPar.yx hCM hJ hW]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : cT S C = B := by
    calc cT S C = cT S C * (adMat F (cT (σ : E →+* E) Y * J) * adMat F X) := by rw [hyx, Matrix.mul_one]
      _ = adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X := by rw [h1, Matrix.mul_assoc]
      _ = B := by rw [Matrix.mul_assoc, hX, ← Matrix.mul_assoc, hyx, Matrix.one_mul]
  rw [h1, h2]

theorem const_centre {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {c : (AF F ⊗[F] E)ˣ} {a : GAd σ J} (ha : IsIdTorusElt σ J X Y (fun _ => c) a) :
    a ∈ levi σ J X Y {Fin.last r} ∧ ∀ m ∈ levi σ J X Y {Fin.last r}, a * m = m * a := by
  have ext : ∀ {m : GAd σ J}, m ∈ levi σ J X Y {Fin.last r} →
      (∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J m).1 * adMat F X = adMat F X * B) ∧
      ∃ C : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J m).1 * adMat F Y = adMat F Y * C := by
    intro m hm
    simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf] at hm
    obtain ⟨⟨B, -, hB⟩, ⟨C, -, hC⟩⟩ := hm (Fin.last r) (Finset.mem_singleton_self _)
    exact ⟨⟨B.1, hB⟩, ⟨C.1, hC⟩⟩
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf]
    intro k hk
    refine ⟨⟨⟨diagonal fun i => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => (((c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩,
      ⟨⟨diagonal fun i => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => ((conjUnit σ c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩⟩
    · ext i j
      have := congrFun (congrFun ha.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
    · ext i j
      have := congrFun (congrFun ha.2.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
  · obtain ⟨⟨B, hB⟩, ⟨C, hC⟩⟩ := ext hm
    obtain ⟨⟨B', hB'⟩, ⟨C', hC'⟩⟩ := ext (inv_mem hm)
    have rY := row_of_stab hCM hJ hW hB hC'
    have rX := row_of_stab hCM hJ (GlobalTheory.IdTorusCent.swap hCM hJ hW) hC hB'
    have dc : ∀ (d : AF F ⊗[F] E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)),
        diagonal (fun _ : Fin (r + 1) => d) * Z = Z * diagonal (fun _ => d) := fun d Z => by
      ext i j; simp [diagonal_mul, mul_diagonal, mul_comm]
    have c1 : (matHom _ σ J m).1 * (adMat F X * diagonal (fun _ : Fin (r + 1) => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) Y * J)) = adMat F X * diagonal (fun _ : Fin (r + 1) => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J m).1 := by
      rw [Matrix.mul_assoc (adMat F X * _), rY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB,
        Matrix.mul_assoc (adMat F X) B, ← dc, ← Matrix.mul_assoc]
    have c2 : (matHom _ σ J m).1 * (adMat F Y * diagonal (fun _ : Fin (r + 1) => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) X * J)) = adMat F Y * diagonal (fun _ : Fin (r + 1) => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) X * J) * (matHom _ σ J m).1 := by
      rw [Matrix.mul_assoc (adMat F Y * _), rX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hC,
        Matrix.mul_assoc (adMat F Y) C, ← dc, ← Matrix.mul_assoc]
    apply matHom_injective
    apply Units.ext
    simp only [map_mul, Units.val_mul, _root_.GlobalTheory.IdTorus.mat_eq_of_isIdTorusElt hCM hJ hW ha, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, c1, c2]

end GlobalTheory.ResidueFlow


open GlobalTheory.IdTorus in
theorem GlobalTheory.ResidueEisenstein.exists_isFlowJ : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ b : ℝ → GAd σ J, IsFlowJ σ J X Y b := by
  intro F E _ _ _ _ _ σ n J r X Y hc hJ hW
  obtain ⟨t, htc, ht⟩ := exists_continuous_isIdTorusElt hc hJ hW
  obtain ⟨l, lc, ladd, -, labs⟩ := exists_real_idele_flow F E σ hc
  have hd : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have cl := fun s : ℝ => GlobalTheory.ResidueFlow.const_centre hc hJ hW (ht fun _ => l (s / ((r + 1 : ℕ) : ℝ)))
  refine ⟨fun s => t fun _ => l (s / ((r + 1 : ℕ) : ℝ)),
    htc.comp (continuous_pi fun _ => lc.comp (continuous_id.div_const _)), fun s s' => ?_, fun s => ?_,
    fun s => (cl s).1, fun s => (cl s).2⟩
  · refine isIdTorusElt_uniq hc hJ hW (ht _) ?_
    have : (fun _ : Fin (r + 1) => l ((s + s') / ((r + 1 : ℕ) : ℝ))) =
        (fun _ => l (s / ((r + 1 : ℕ) : ℝ))) * fun _ => l (s' / ((r + 1 : ℕ) : ℝ)) := by
      funext k; rw [add_div, ladd]; rfl
    rw [this]; exact isIdTorusElt_mul (ht _) (ht _)
  · refine ⟨Units.map (Matrix.scalar (Fin (r + 1))).toMonoidHom (l (s / ((r + 1 : ℕ) : ℝ))), (ht _).1, ?_⟩
    have : Matrix.GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin (r + 1))).toMonoidHom (l (s / ((r + 1 : ℕ) : ℝ)))) =
        l (s / ((r + 1 : ℕ) : ℝ)) ^ (r + 1) := by
      apply Units.ext
      change Matrix.det (Matrix.diagonal fun _ : Fin (r + 1) => (l (s / ((r + 1 : ℕ) : ℝ))).1) = _
      rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val]
    rw [this, map_pow, NNReal.coe_pow, labs, ← Real.exp_nat_mul, mul_div_cancel₀ _ hd]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEndomorphismOfConjugateAdjointForm
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

namespace GlobalTheory.GramAdj

theorem exists_endo_of_adjoint :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (β : D.La → D.La → ℤ), (∀ x y z, β (x + y) z = β x z + β y z) → (∀ x y z, β x (y + z) = β x y + β x z) → (∀ (s : 𝓞 E) x y, β (s • x) y = β x (H.bar s • y)) → ∃ γ : D.La →+ D.La, (∀ (s : 𝓞 E) x, γ (s • x) = s • γ x) ∧ ∀ x y, β x y = D.EF (γ x) y := by
  intro E _ _ _ H D β hl hr hs
  let f : D.La → (D.La →ₗ[ℤ] ℤ) := fun x => (AddMonoidHom.mk' (β x) (hr x)).toIntLinearMap
  have hf : ∀ x y, f x y = β x y := fun _ _ => rfl
  let e := Equiv.ofBijective D.EF D.unimod
  have he : ∀ g, D.EF (e.symm g) = g := fun g => e.apply_symm_apply g
  have key : ∀ x y, D.EF (e.symm (f x)) y = β x y := fun x y => by rw [he, hf]
  have hadd : ∀ x x', e.symm (f (x + x')) = e.symm (f x) + e.symm (f x') := by
    intro x x'
    apply D.unimod.1
    ext y
    simp only [map_add (f := _), LinearMap.add_apply, key, hl]
  refine ⟨AddMonoidHom.mk' (fun x => e.symm (f x)) hadd, ?_, ?_⟩
  · intro s x
    show e.symm (f (s • x)) = s • e.symm (f x)
    apply D.unimod.1
    ext y
    rw [key, hs, ← key, D.adj]
  · intro x y
    show β x y = D.EF (e.symm (f x)) y
    rw [key]

end GlobalTheory.GramAdj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBoundDiagonalExponentsRationalPoint
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

theorem exists_bound_exponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∀ W : Set (GAd σ J), IsCompact W → ∃ m₀ : ℕ, ∀ q ∈ fixG σ J C, ∀ l : Fin j → ℤ, ∀ w ∈ W, q * lv (tor F E l) * w ∈ ratPts σ J → ∀ i, -(m₀ : ℤ) ≤ l i := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hlv W hW
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  set P : Matrix (Fin j) (Fin n) (AF F ⊗[F] E) := adMat F (cT (σ : E →+* E) C * J) with hP
  have hq : ∀ q ∈ fixG σ J C, P * (matHom _ σ J q).1 = P := by
    intro q hq
    have h1 : (matHom _ σ J q⁻¹).1 * adMat F C = adMat F C * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]; exact inv_mem hq
    have h := form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at h
  have hl : ∀ α, P * (matHom _ σ J (lv α)).1 = cT (sigR (AF F) σ) (α⁻¹).1 * P := by
    intro α
    have h := form_mul_of_mul_cols (hlv.onC α⁻¹)
    rwa [map_inv lv α, inv_inv] at h
  have hc : Continuous fun w : GAd σ J => P * (matHom _ σ J w).1 :=
    continuous_const.matrix_mul (Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J).continuous)
  have hb : GlobalTheory.Eis.Conv.Bdd fun w : W => (w : GAd σ J) := ⟨W, hW, fun w => w.2⟩
  obtain ⟨Ω, hΩ, hΩw⟩ := GlobalTheory.Eis.Conv.Bdd.entries (GlobalTheory.Eis.Conv.Bdd.map hb hc)
  obtain ⟨m₀, hm₀⟩ := (GlobalTheory.T.compact_adeles_rational_points_finite_eventually_zero F E Ω hΩ).2
  refine ⟨m₀, fun q hqm l w hw hg i => ?_⟩
  have ht : cT (sigR (AF F) σ) (tor F E l)⁻¹.1 = (tor F E l)⁻¹.1 :=
    congrArg Units.val (GlobalTheory.Eis.Conv.cti_dg (GlobalTheory.Eis.Conv.sigR_halfE σ) l)
  have h1 : P * (matHom _ σ J (q * lv (tor F E l) * w)).1 = (tor F E l)⁻¹.1 * (P * (matHom _ σ J w).1) := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hq q hqm, hl, ht,
      Matrix.mul_assoc]
  generalize q * lv (tor F E l) * w = g at hg h1
  have hg' : matHom _ σ J g ∈ HFin (AF F) σ J := Subgroup.mem_subgroupOf.1 hg
  obtain ⟨γ, -, e⟩ := Subgroup.mem_map.1 hg'
  have hm : (matHom _ σ J g).1 = γ.1.map (inclR (F := F) (AF F)) := by
    rw [← e]; rfl
  have hy : (cT (σ : E →+* E) C * J * γ.1).map (inclR (F := F) (AF F)) = P * (matHom _ σ J g).1 := by
    rw [hm, Matrix.map_mul]
  have hrow : ¬∀ x, (cT (σ : E →+* E) C * J * γ.1) i x = 0 :=
    GlobalTheory.GodementSectionReduction.row_ne_zero (N := γ⁻¹.1 * D) (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ.1, Units.mul_inv, Matrix.one_mul, hF.cd]) i
  have hrow' : ¬∀ x, (cT (σ : E →+* E) C * J * γ.1).map (inclR (F := F) (AF F)) i x = 0 := fun h =>
    hrow fun x => by
      have := h x
      rwa [Matrix.map_apply, map_eq_zero_iff _ GlobalTheory.AutFunCompare.inclA_injective] at this
  exact GlobalTheory.GodementSectionReduction.bound_aux (inclR (F := F) (AF F)) hm₀ (fun i x => hΩw ⟨w, hw⟩ i x) (hy.trans h1) i hrow'

end GlobalTheory.SphEis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalAboveOfDvdNormHost
section
open NumberField

namespace GlobalTheory.MaximalIdealDividingNorm

theorem exists_maximal_above_of_dvd_norm {K : Type*} [Field K] [NumberField K]
    (𝔪 : Ideal (𝓞 K)) {p : ℕ} (hp : p.Prime) (hd : p ∣ Ideal.absNorm 𝔪) :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ 𝔪 ≤ P ∧ (p : 𝓞 K) ∈ P := by
  obtain ⟨P, hmax, hunder, hdiv⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp 𝔪 hd
  refine ⟨P, hmax, Ideal.le_of_dvd hdiv, ?_⟩
  have h1 : (p : ℤ) ∈ Ideal.under ℤ P := by
    rw [hunder]
    exact Ideal.mem_span_singleton_self _
  have h2 : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P := Ideal.mem_comap.mp h1
  rwa [map_natCast] at h2

theorem exists_maximal_above_of_dvd_norm_host (D : Formalism.BasicNotions.D7)
    (𝔪 : Ideal (𝓞 (Formalism.BasicNotions.D7.host D).E)) (_h𝔪 : 𝔪 ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Ideal.absNorm 𝔪) :
    ∃ P : Ideal (𝓞 (Formalism.BasicNotions.D7.host D).E),
      P.IsMaximal ∧ 𝔪 ≤ P ∧ (p : 𝓞 (Formalism.BasicNotions.D7.host D).E) ∈ P :=
  exists_maximal_above_of_dvd_norm 𝔪 hp hd

end GlobalTheory.MaximalIdealDividingNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingMapsLiftVerticalDeformationsAffineStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringMaps_lift_vertical_deformations_affine : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (k : X.F.J) (W : M.X.Opens) (hW : IsAffineOpen W)
    (hle : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k), ∃ e : VIx Dw → (Γ(M.X, W) →+* DualNumber Γ(M.X, W)), (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W) →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW) ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b : VIx Dw, ∃ w : FrPt Xo c (DualNumber K),
          IsVert Q (Pi.single b.toF (1 : K)) w ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW ≫ toFlag M = X.ptY w := by
  first | exact @GlobalTheory.CompHS.exists_vertLift | exact GlobalTheory.CompHS.exists_vertLift | (intros; apply GlobalTheory.CompHS.exists_vertLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBasisSectionsAbelianSchemeOverDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.exists_veryAmpleBy_basis_of_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (M : LB G.left) (m : ℕ) (t₀ : Fin (m + 1) → M.Sec), M.IsLB → GlobalTheory.AbLaw.VeryAmpleBy G.hom M t₀ → ∃ (N : ℕ) (t : Fin (N + 1) → M.Sec), GlobalTheory.AbLaw.VeryAmpleBy G.hom M t ∧ ∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, GlobalTheory.AbLaw.cst G.hom ⊤ (c j) • t j := by
  intro W _ _ _ G _ hG M m t₀ hM hv
  have hflat : Flat G.hom := by
    haveI := hG.smooth
    infer_instance
  obtain ⟨n, t, ht⟩ := _root_.GlobalTheory.AbLaw.exists_basis_sec_of_isDiscreteValuationRing W G.left G.hom M hflat ⟨M, hM, m, t₀, hv⟩ hM
  have hne : Nonempty G.left := by
    obtain ⟨x⟩ : Nonempty (Sp W) := inferInstance
    exact ⟨(η[G]).left x⟩
  obtain ⟨x⟩ := hne
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hv.1.ge (Set.mem_univ x))
  have hn : n ≠ 0 := by
    rintro rfl
    obtain ⟨c, hc, -⟩ := ht (t₀ i₀)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hc
    rw [hc] at hi₀
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi₀
    have hk' : x ∈ G.left.basicOpen (0 : Γ(G.left, M.U k)) := hk
    rw [Scheme.basicOpen_zero] at hk'
    exact hk'
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  choose a ha using fun i => (ht (t₀ i)).exists
  exact ⟨N, t, _root_.GlobalTheory.veryAmpleBy_of_span W G.left G.hom M m N t₀ t a hM hv ha, ht⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridConductorIdealCMIsCoprimeHalfDifferent
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.StdDatum.HalfDiff

theorem condE_isCoprime_bb {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (h1 : Nat.Coprime D.host.pde (D.host.QS * D.host.q))
    (h2 : Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) : IsCoprime (condE P) D.host.𝔟 :=
  (condE_isCoprime_halfDifferent P ⟨h1, h2⟩).1

end GlobalTheory.FunObj.StdDatum.HalfDiff
end
end

