module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0550
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0584
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0591
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0579
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
public import GroundTheory.AutomorphicForms.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.Bundle0001
public import Formalism.GelfandTransference.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousIpFst
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist

variable {D : D7} {a n r t : ℕ}

theorem continuous_qv (V : HSp D) (b₀ : HermE D r) :
    Continuous (fun z : Mx D V.rank r × Mx D V.rank t => qv V b₀ z) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hip : ∀ {X : Type} [TopologicalSpace X] {a c : ℕ} {f : X → Mx D V.rank a} {g : X → Mx D V.rank c},
      Continuous f → Continuous g → Continuous (fun x => ip V (f x) (g x)) := by
    intro X _ a c f g hf hg
    unfold ip
    exact (continuous_adj.comp hf).matrix_mul (continuous_const.matrix_mul hg)
  have hyv : Continuous (fun z : Mx D V.rank r × Mx D V.rank t => yv V b₀ z) := by
    unfold yv
    exact continuous_const.matrix_mul (hip continuous_fst continuous_snd)
  have hpr : Continuous (fun x : Mx D V.rank r × Mx D V.rank t => pr b₀ (yv V b₀ x) (yv V b₀ x)) := by
    unfold pr
    exact (continuous_adj.comp hyv).matrix_mul (continuous_const.matrix_mul hyv)
  unfold qv
  have h1 : Continuous (fun z : Mx D V.rank r × Mx D V.rank t => ip V z.2 z.2) := hip continuous_snd continuous_snd
  have hn : ContinuousNeg (AE D) := IsTopologicalRing.toContinuousNeg
  have ha : ContinuousAdd (AE D) := IsTopologicalSemiring.toContinuousAdd
  exact continuous_matrix fun i j => (h1.matrix_elem i j).add (hpr.matrix_elem i j).neg |>.congr fun z => (sub_eq_add_neg _ _).symm

theorem continuous_ip_fst (V : HSp D) :
    Continuous (fun z : Mx D V.rank r × Mx D V.rank t => ip V z.1 z.1) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold ip
  exact (continuous_adj.comp continuous_fst).matrix_mul (continuous_const.matrix_mul continuous_fst)

theorem continuous_pch₂ {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {X : Type} [TopologicalSpace X]
    {f g : X → Mx D t t} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => pch ψ (f x) (g x)) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have htr : Continuous (trA : AE D → AF D.host.F) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hhalf : Continuous (halfTr : AE D → AF D.host.F) := by
    unfold halfTr
    exact continuous_const.mul htr
  unfold pch
  exact hψ.1.comp (hhalf.comp (hf.matrix_mul hg).matrix_trace)

theorem isClosed_fixed (e : AE D) :
    IsClosed {z : Mx D a r × Mx D a t | e • z.1 = z.1 ∧ e • z.2 = z.2} := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, h1, -⟩ := GlobalTheory.CompanionTheory.ColumnSplitting.top_mx (D := D) a r
  obtain ⟨-, -, -, h2, -⟩ := GlobalTheory.CompanionTheory.ColumnSplitting.top_mx (D := D) a t
  have c1 : Continuous fun x : Mx D a r => e • x := continuous_const_smul e
  have c2 : Continuous fun x : Mx D a t => e • x := continuous_const_smul e
  exact (isClosed_eq (c1.comp continuous_fst) continuous_fst).inter (isClosed_eq (c2.comp continuous_snd) continuous_snd)

theorem conj_cancel (g : GL (Fin t) (AE D)) (q : Mx D t t) :
    mm (mm (adj (g⁻¹).1) (mm (mm (adj g.1) q) g.1)) (g⁻¹).1 = q := by
  have h1 : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : (adj (g⁻¹).1 * adj g.1 : Mx D t t) = 1 := by
    have := adj_mul (D := D) g.1 (g⁻¹).1
    rw [← this, h1, adj_one_r]
  simp only [mm]
  calc _ = (adj (g⁻¹).1 * adj g.1 : Mx D t t) * q * (g.1 * (g⁻¹).1) := by simp only [Matrix.mul_assoc]
    _ = q := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem comp_mem {θ : InfFam D} (hθ : IsInfFam θ) {hn : r + t = n} {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e)
    (hR : ∀ f ∈ algA (a := a) θ hn S e,
      ∃ Φ ∈ schwartzA θ a n, Good S e Φ ∧ HasCompactSupport Φ ∧ f = fun z => Φ (jn hn z.1.1 z.1.2))
    (hSt : AlgStab) (h : GL (Fin a) (AE D)) (g : GL (Fin n) (AE D)) (hh : e • (h.1 - 1) = h.1 - 1) (hg : e • (g.1 - 1) = g.1 - 1)
    (Θ : XS D a r t e → XS D a r t e)
    (hΘ : ∀ z, jn hn (Θ z).1.1 (Θ z).1.2 = mm (mm h.1 (jn hn z.1.1 z.1.2)) g.1) (f : XS D a r t e → ℂ)
    (hf : f ∈ algA (a := a) θ hn S e) : f ∘ Θ ∈ algA (a := a) θ hn S e := by
  obtain ⟨Φ, h1, h2, h3, rfl⟩ := hR f hf
  obtain ⟨m1, m2, m3⟩ := hSt D θ hθ a n S e hS h g hh hg Φ h1 h2 h3
  refine Submodule.subset_span ⟨_, m1, m2, m3, ?_⟩
  funext z
  simp only [Function.comp, hΘ]

theorem trans_int₁ {X N : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace N] [MeasurableSpace N]
    [BorelSpace N] (σ : Measure X) (lam : Measure N) (k : N → X → ℂ) (f : X → ℂ) (Θ : X ≃ₜ X)
    (h₁ : σ.map Θ = σ) (hk : ∀ x, ∀ᵐ z ∂σ, k x z = k x (Θ z)) :
    ∫ x, ∫ z, f (Θ z) * k x z ∂σ ∂lam = ((1 : ℝ≥0) : ℂ) * ∫ x, ∫ z, f z * k x z ∂σ ∂lam := by
  have := trans_int σ lam k f Θ (Homeomorph.refl N) 1 1 (by rw [one_smul]; exact h₁) (by simp) hk
  simpa using this

theorem kap (A : ℝ≥0) (hA : A ≠ 0) (N r t : ℕ) (hN : N = r + 2 * t) : (A⁻¹) ^ N * ((A⁻¹)⁻¹) ^ t = (A⁻¹) ^ (r + t) := by
  subst hN
  rw [inv_inv, two_mul, ← add_assoc, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hA, one_pow, mul_one]

theorem absA_inv (D : D7) (u : (AE D)ˣ) : absA D u⁻¹ = (absA D u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, inv_mul_cancel, map_one]

theorem absA_ne (D : D7) (u : (AE D)ˣ) : absA D u ≠ 0 := by
  have h1 : absA D u * absA D u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  intro h
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

end GlobalTheory.CompanionTheory.OrbExist

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverIntersectionGradedVanish
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CapVan

theorem capO_eq_iInf_image {X : Scheme.{0}} {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → X.Opens) {m : ℕ}
    (i : Fin m → ι) : capO V i = ⨅ α ∈ Finset.image i Finset.univ, V α := by
  show (⨅ a, V (i a)) = _
  apply le_antisymm
  · refine le_iInf₂ fun α hα => ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
    exact iInf_le _ a
  · exact le_iInf fun a => iInf₂_le (i a) (Finset.mem_image_of_mem i (Finset.mem_univ a))

theorem van {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι) (r : ℕ) (hr : r ≠ a) :
    Subsingleton (HU (Fk q U a) (capT (Vk q U a) i) r) := by
  classical
  obtain ⟨e⟩ := _root_.GlobalTheory.CompanionTheory.CapKC.cap_kc q U a n i r
  have hV : IsAffineOpen (capO U.U i) := by
    rw [capO_eq_iInf_image]
    exact U.inter _ ⟨i 0, Finset.mem_image_of_mem i (Finset.mem_univ 0)⟩
  haveI := CrystallineSemistableComparison.Pb.gr_aff q (capO U.U i) hV (a + 1) a r (Nat.lt_succ_self a) hr
  exact e.injective.subsingleton

end GlobalTheory.CompanionTheory.CapVan
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverStarIsCosieve
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.OmGlob

theorem vk_cosieve {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a : ℕ) (α : U.ι) :
    Cosieve (Vk q U a α) :=
  fun _ _ φ h => Site.inU_hom φ.hom h

end GlobalTheory.CompanionTheory.OmGlob
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionCompact
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspidalCompact

theorem isCompactOperator_repOp_Rcusp (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    IsCompactOperator (repOp (Rcusp μ) μ f) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact GlobalTheory.CompanionTheory.CuspRank.isCompactOperator_repOp_Rcusp_zero E μ f
  · let ν : Measure (GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a)) := Measure.haar
    have : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
    have htransfer := GlobalTheory.T.cuspidal_L2_norm_one_isometry E a ha μ ν
    obtain ⟨Φ, c, hc0, hΦ, hint⟩ := htransfer
    obtain ⟨f₁, hf₁⟩ := hint f hf hc
    exact GlobalTheory.CompanionTheory.CompactOperators.isCompactOperator_of_scaled_isometric_intertwiner (repOp (Rcusp μ) μ f) _ Φ c hc0 hΦ hf₁
      (GroundTheory.Automorphic.CuspidalSpectrum.isCompactOperator_cuspRep (K := E) (n := a) ν f₁)

end GlobalTheory.CompanionTheory.CuspidalCompact
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZero
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.CuspNotInd

open GroundTheory.Automorphic.Parabolic (levi parabolicInd)
open GroundTheory.Automorphic.Iwasawa (blockUpper)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unipotentRadical_ne_bot {n : ℕ} {γ : Fin n → ℕ} (hγ : ∃ i j, γ i ≠ γ j) :
    GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ ≠ ⊥ := by
  have h : ∃ i j, γ i < γ j := by
    obtain ⟨i, j, hij⟩ := hγ
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h⟩
    · exact ⟨j, i, h⟩
  obtain ⟨i, j, hij⟩ := h
  have hne : i ≠ j := fun e => hij.ne (congrArg γ e)
  let g : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j 1)
    (by rw [Matrix.det_transvection_of_ne _ _ hne]; exact one_ne_zero)
  have hg : ∀ a b, (g : Matrix (Fin n) (Fin n) k) a b = (1 : Matrix (Fin n) (Fin n) k) a b +
      Matrix.single i j (1 : k) a b := fun a b => rfl
  intro hbot
  have hmem : g ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ := by
    rw [GroundTheory.Automorphic.Parabolic.mem_unipotentRadical, GroundTheory.Automorphic.Iwasawa.mem_blockUpper]
    refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
    · rw [hg, Matrix.one_apply_ne (fun e => hab.ne (by rw [e])), Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact absurd hab hij.not_gt
    · rw [hg, Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact hij.ne hab
  rw [hbot, Subgroup.mem_bot] at hmem
  have h3 := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hmem
  simp only [hg, Matrix.one_apply_ne hne, Matrix.single_apply_same, zero_add, Units.val_one] at h3
  exact one_ne_zero h3

theorem isSupercuspidal_of_isCuspidal {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (h : IsCuspidal π) :
    GroundTheory.Automorphic.Parabolic.IsSupercuspidal π := by
  intro γ hγ
  classical
  let s : ℕ := Finset.univ.sup γ + 1
  let r : Fin n → Fin s := fun i => ⟨γ i, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))⟩
  let d : Fin s → ℕ := fun a => Fintype.card {i // r i = a}
  let e : (Σ a, Fin (d a)) ≃ Fin n :=
    (Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // r i = a}).symm).trans (Equiv.sigmaFiberEquiv r)
  have hblk : ∀ i, GlobalTheory.SmGL.blk e i = r i := fun i => by
    show (e.symm i).1 = r i
    rfl
  have hβ : ∀ i j, γ i < γ j ↔ GlobalTheory.SmGL.blk e i < GlobalTheory.SmGL.blk e j := fun i j => by
    rw [hblk, hblk]; exact Iff.rfl
  have hN : ∀ g, g ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ ↔ g ∈ unipRad k e :=
    GlobalTheory.CompanionTheory.JacquetBridge.mem_unipotentRadical_iff e hβ
  have hne : unipRad k e ≠ ⊥ := fun hb => unipotentRadical_ne_bot (k := k) hγ
    (by rw [eq_bot_iff]; intro g hg; rw [← hb]; exact (hN g).1 hg)
  have htop := Submodule.Quotient.subsingleton_iff.1 (h.2 s d e hne)
  let ρ' := π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ).subtype
  have hle : twKer π (unipRad k e) 1 ≤ LinearMap.ker (Representation.Coinvariants.mk ρ') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    have : Representation.Coinvariants.mk ρ' (ρ' ⟨u, (hN _).2 u.2⟩ v) = Representation.Coinvariants.mk ρ' v :=
      Representation.Coinvariants.mk_self_apply _ _ _
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, MonoidHom.one_apply, Units.val_one, one_smul]
    exact sub_eq_zero.2 this
  have hz : ∀ y : Representation.Coinvariants ρ', y = 0 := fun y => by
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective ρ' y
    exact hle (htop ▸ Submodule.mem_top)
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

theorem isSubquotient_carry {r : ℕ} {d : Fin r → ℕ} {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ (GL (Fin (∑ a, d a)) k) V}
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (e : (Σ a, Fin (d a)) ≃ Fin (∑ a, d a))
    (he : e = GlobalTheory.CompanionTheory.BZInd.stdE d) (h : IsSubquotient π (parInd e ρ)) :
    IsSubquotient π (parabolicInd k (∑ a, d a) (GlobalTheory.CompanionTheory.BZInd.pos d) (GlobalTheory.CompanionTheory.BZInd.carry ρ)) := by
  subst he
  exact h.trans (.of_injective _ (GlobalTheory.CompanionTheory.BZInd.toIndMap_injective ρ))

theorem isIrreducible_carry {r : ℕ} {d : Fin r → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (h : ρ.IsIrreducible) :
    (GlobalTheory.CompanionTheory.BZInd.carry ρ).IsIrreducible :=
  isIrreducible_twist (GlobalTheory.LocCompSplit.isIrreducible_comp_of_surjective ρ _ GlobalTheory.CompanionTheory.BZInd.leviTo_surjective h) _

theorem isSmooth_carry {r : ℕ} {d : Fin r → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (h : IsSmooth ρ) :
    IsSmooth (GlobalTheory.CompanionTheory.BZInd.carry ρ) :=
  isSmooth_twist (isSmooth_comp h _ GlobalTheory.CompanionTheory.BZInd.continuous_leviTo) GlobalTheory.CompanionTheory.BZInd.isSmoothChar_adj

theorem exists_pos_ne {r : ℕ} {d : Fin r → ℕ} (h2 : 2 ≤ r) (hd : ∀ a, 0 < d a) :
    ∃ i j, GlobalTheory.CompanionTheory.BZInd.pos d i ≠ GlobalTheory.CompanionTheory.BZInd.pos d j := by
  let a : Fin r := ⟨0, by omega⟩
  let b : Fin r := ⟨1, by omega⟩
  refine ⟨GlobalTheory.CompanionTheory.BZInd.stdE d ⟨a, ⟨0, hd a⟩⟩, GlobalTheory.CompanionTheory.BZInd.stdE d ⟨b, ⟨0, hd b⟩⟩, ?_⟩
  rw [GlobalTheory.CompanionTheory.BZInd.pos_stdE, GlobalTheory.CompanionTheory.BZInd.pos_stdE]
  simp [a, b]

theorem jhMult_eq_zero_of_isCusp : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (ρ : IrrGL (k := k)) {h : ℕ}
    (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = ρ.1), ρ.IsCusp → 2 ≤ h → (∀ a, 0 < (x a).1) →
    jhMult ρ.rep (prodIrr x hd) = 0 := by
  intro k _ _ _ _ hA ρ h x hd hc h2 hpos
  obtain ⟨N, c⟩ := ρ
  dsimp only at hd
  subst hd
  by_contra hne
  have hsub := jhMult_ne_zero_iff.1 hne
  let ρ₀ : IrrGL (k := k) := ⟨_, c⟩
  have hs2 := isSubquotient_carry (d := fun a => (x a).1) (piTensor fun a => (x a).rep) _
    (Equiv.ext fun y => by simp [stdBlocks, GlobalTheory.CompanionTheory.BZInd.stdE]) hsub
  obtain ⟨A, p, hp⟩ := hs2
  haveI : ρ₀.rep.IsIrreducible := ρ₀.2.rep.irr
  haveI := isIrreducible_carry (d := fun a => (x a).1) _ (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA x)
  exact GroundTheory.Automorphic.Parabolic.not_surjective_of_isIrreducible (π := ρ₀.rep) ρ₀.2.rep.smooth
    (isSupercuspidal_of_isCuspidal hc.2) (exists_pos_ne h2 hpos)
    (isSmooth_carry _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)) A p hp

end GlobalTheory.CompanionTheory.CuspNotInd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableCoeffRowAct
section
noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmHol

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem differentiable_entry {r : ℕ} (a b : Fin r) :
    Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ => M a b :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a b)).differentiable

theorem differentiable_det {r : ℕ} :
    Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ => M.det := by
  simp only [Matrix.det_apply']
  refine Differentiable.fun_sum fun σ _ => Differentiable.const_mul ?_ _
  have h : ∀ t : Finset (Fin r), Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ => ∏ i ∈ t, M (σ i) i := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (differentiable_entry (σ a) a).mul ih
  exact h Finset.univ

theorem differentiable_coeff_rowAct {r m : ℕ} (f : MvPolynomial (Fin r × Fin m) ℂ) :
    ∀ s : (Fin r × Fin m) →₀ ℕ, Differentiable ℂ fun M : Matrix (Fin r) (Fin r) ℂ =>
      AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ f) s := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro s
    simpa [MvPolynomial.algebraMap_eq] using
      (differentiable_const (AddMonoidAlgebra.coeff (MvPolynomial.C a : MvPolynomial (Fin r × Fin m) ℂ) s) :
        Differentiable ℂ fun _ : Matrix (Fin r) (Fin r) ℂ => _)
  | add p q hp hq =>
    intro s
    simp only [map_add (f := _), MvPolynomial.coeff_add]
    exact (hp s).add (hq s)
  | mul_X p v hp =>
    intro s
    have key : ∀ M : Matrix (Fin r) (Fin r) ℂ,
        AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ (p * MvPolynomial.X v)) s =
        ∑ b : Fin r, M b v.1 * (if (b, v.2) ∈ s.support then
          AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ p) (s - Finsupp.single (b, v.2) 1) else 0) := by
      intro M
      have hX : Formalism.GradedWeylDivisibility.rowAct ℂ (n := m) Mᵀ (MvPolynomial.X v) =
          ∑ b : Fin r, MvPolynomial.C (M b v.1) * MvPolynomial.X (b, v.2) := by
        simp [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]
      rw [map_mul, hX, Finset.mul_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X']
    simp only [key]
    refine Differentiable.fun_sum fun b _ => ?_
    refine (differentiable_entry b v.1).mul ?_
    split_ifs
    · exact hp _
    · exact differentiable_const _

theorem detPow_nonsingInvUnit {n : ℕ} {x : Mat n} (h : IsUnit x.det) (c : ℤ) :
    Formalism.BasicNotions.detPow ℂ n (Matrix.nonsingInvUnit x h) c = x.det ^ c := by
  have e : ((Matrix.GeneralLinearGroup.det (Matrix.nonsingInvUnit x h) : ℂˣ) : ℂ) = x.det := rfl
  rw [Formalism.BasicNotions.detPow, Units.val_zpow_eq_zpow_val, e]

theorem holRm (n : ℕ) (lam : Fin n → ℤ) : HolRm lam := by
  intro i j g hg
  obtain ⟨S, c, hc⟩ := GlobalTheory.CompanionTheory.WInfCont.exists_finset_factor (Formalism.BasicNotions.nablaSq ℂ n (dw lam)) ((wb lam).coord i)
  have hev : (fun x : Mat n => Rm lam x i j) =ᶠ[𝓝 g] fun x : Mat n =>
      ∑ s : S, c s * (x.det ^ (dw lam).detShift *
        AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) xᵀ (wb lam j).1) s.1) := by
    filter_upwards [isOpen_GLs.mem_nhds hg] with x hx
    have hu := isUnit_det_of_mem hx
    rw [Rm_of_unit lam hu, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply, hc]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [GlobalTheory.Branching.sqRep_coe, Formalism.BasicNotions.sqAct, MvPolynomial.coeff_smul, smul_eq_mul,
      detPow_nonsingInvUnit hu]
    rfl
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  refine DifferentiableAt.fun_sum fun s _ => DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.mul ?_ (differentiable_coeff_rowAct _ _ _)
  exact (differentiable_det g).zpow (Or.inl hg)

end GlobalTheory.CompanionTheory.RmHol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexMapLeadCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechSerre

theorem leadE_map : ∀ {R : Type} [CommRing R] (K L : DCx.{1} R) (φ : DCx.Hom K L (RingHom.id R)) (a j : ℕ) (z : Zf K (a + j) j),
    ∃ z' : Zf L (a + j) j, clsZ L (a + j) j z' = φ.tot.mapH (a + j) (clsZ K (a + j) j z) ∧
      ∃ (y : (L.col j).H a) (hy : (colH L a).d j y = 0) (y₀ : (K.col j).H a) (hy₀ : (colH K a).d j y₀ = 0),
        leadE K j a z = (colH K a).cls y₀ hy₀ ∧ leadE L j a z' = (colH L a).cls y hy ∧ y = (φ.col j).mapH a y₀ := by
  intro R _ K L φ a j z
  have hc : L.tot.d (a + j) (φ.tot.f (a + j) z.1.1) = 0 := by
    rw [φ.tot.comm, show K.tot.d (a + j) z.1.1 = 0 from z.1.2, map_zero]
  have hvan : ∀ p q, p < j → (φ.tot.f (a + j) z.1.1).1 p q = 0 := by
    intro p q hp
    change φ.f p q (z.1.1.1 p q) = 0
    rw [z.2 p q hp, map_zero]
  let z' : Zf L (a + j) j := ⟨⟨φ.tot.f (a + j) z.1.1, hc⟩, hvan⟩
  have hv : (K.col j).d a (z.1.1.1 j a) = 0 := dv_lead K z.1.1.1 (D_zero K z.1) j a z.2
  have hv' : (L.col j).d a ((φ.col j).f a (z.1.1.1 j a)) = 0 := by
    rw [(φ.col j).comm, hv, map_zero]
  have hy : leadC L j a z' = (φ.col j).mapH a (leadC K j a z) := by
    rw [leadC_eq K j a z hv, P.mapH_cls _ a _ hv hv']
    rfl
  refine ⟨z', ?_, leadC L j a z', leadC_mem L j a z', leadC K j a z, leadC_mem K j a z,
    leadE_eq K j a z, leadE_eq L j a z', hy⟩
  exact (P.mapH_cls φ.tot (a + j) z.1.1 z.1.2 hc).symm

end GlobalTheory.CompanionTheory.CechSerre
end
end

