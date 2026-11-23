module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedCartierDivisorOfSncClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatSmulMemLattice
section
namespace GlobalTheory.NatSmulMemLattice

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ (n : ℕ) (a : 𝓞 E), 0 < n ∧ (a : E) = (n : E) * c := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  have h2 : IsIntegral ℤ ((y : E) * (y • c)) := by
    have h3 : IsIntegral ℤ (y : E) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := y))
    exact h3.mul hy
  refine ⟨y.natAbs * y.natAbs, ⟨_, h2⟩, ?_, ?_⟩
  · have := Int.natAbs_pos.2 hy0
    positivity
  · have h4 : ((y.natAbs * y.natAbs : ℕ) : E) = (y : E) * (y : E) := by
      have h5 : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := Int.natAbs_mul_self
      have h6 := congrArg (Int.cast : ℤ → E) h5
      rw [Int.cast_natCast, Int.cast_mul] at h6
      exact h6
    rw [h4]
    change (y : E) * (y • c) = _
    rw [zsmul_eq_mul, mul_assoc]

theorem exists_nat_smul_mem {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (L : Submodule (𝓞 E) W)
    (hL : Submodule.span E (L : Set W) = ⊤) (v : W) :
    ∃ d : ℕ, 0 < d ∧ (d : 𝓞 E) • v ∈ L := by
  have hv : v ∈ Submodule.span E (L : Set W) := hL ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add, Nat.cast_mul]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem _ hx
    · rw [mul_smul]
      exact L.smul_mem _ hy
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨n, e, hn, he⟩ := exists_nat_mul_integral c
    refine ⟨a * n, Nat.mul_pos ha hn, ?_⟩
    have key : ((a * n : ℕ) : 𝓞 E) • c • x = e • (a : 𝓞 E) • x := by
      rw [← algebraMap_smul E e, ← algebraMap_smul E (a : 𝓞 E),
        ← algebraMap_smul E ((a * n : ℕ) : 𝓞 E), smul_smul, smul_smul]
      congr 1
      have he' : algebraMap (𝓞 E) E e = (n : E) * c := he
      rw [he', map_natCast, map_natCast, Nat.cast_mul]
      ring
    rw [key]
    exact L.smul_mem _ hx

theorem exists_nat_smul_mem_lattice {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (v : Formalism.BasicNotions.HSpace.V V) :
    ∃ d : ℕ, 0 < d ∧ (d : 𝓞 (Formalism.BasicNotions.D7.host D).E) • v ∈ Formalism.BasicNotions.HSpace.L0 V :=
  by
    let E := (Formalism.BasicNotions.D7.host D).E
    let f := (V.hT v).restrictScalars (𝓞 E)
    obtain ⟨d, hd, hint⟩ := FractionalIdeal.isFractional_of_fg
      (S := nonZeroDivisors (𝓞 E)) (V.standardTuple_isLattice.fg.map f)
    have hd0 : (d : E) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hd
    obtain ⟨n, a, hn, ha⟩ := exists_nat_mul_integral (d : E)⁻¹
    refine ⟨n, hn, ?_⟩
    rw [← V.baseLattice_isUnimodular]
    change (n : 𝓞 E) • v ∈ Formalism.E.hdual V.hT V.L0
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
    intro y hy
    obtain ⟨b, hb⟩ := hint (V.hT v y) ⟨y, hy, rfl⟩
    have hb' : (b : E) = (d : E) * V.hT v y := hb
    have hab : ((a * b : 𝓞 E) : E) = (n : E) * V.hT v y := by
      change (a : E) * (b : E) = _
      rw [ha, hb']
      field_simp
    have hs : IsIntegral ℤ (star ((n : E) * V.hT v y)) := by
      rw [← hab]
      exact (a * b).2.map (starRingEnd E).toIntAlgHom
    apply Submodule.mem_one.2
    refine ⟨⟨_, ?_⟩, rfl⟩
    change IsIntegral ℤ _
    have hh := V.herm.eq y v
    simp only [star_mul, star_natCast] at hs
    have hh' : star (V.hT v y) = V.hT y v := by
      rw [← hh]
      exact star_star _
    rw [hh'] at hs
    simpa [map_smul, Algebra.smul_def, mul_comm] using hs

end GlobalTheory.NatSmulMemLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunction
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.VacReal

open GlobalTheory.ChainFr GlobalTheory.Size

theorem ptF_zero {D : D7} {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (P : PolF D W.rank V.rank) : ptF ψ θ A B 0 P = 0 := by
  have hd : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z 0 = 0 := by
    intro τ z
    funext w
    simp [Formalism.IndefR.Datum.dRho, heisO]
  have : pureTensorO ψ θ V W A.cart B.cart A.onb B.onb 0 = 0 := by
    unfold pureTensorO pureTensorL
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [Module.Basis.constr_basis]
    show opPow _ k 0 = 0
    unfold opPow
    induction Multiset.toList (Finsupp.toMultiset k) with
    | nil => rfl
    | cons a l ih => rw [List.foldr_cons, ih]; simp [aPlusAll, aPlus, crea, hd]
  unfold ptF
  rw [this]
  rfl

theorem exists_isVacF_ne_zero : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → f ≠ 0 →
      ∃ f₀, GlobalTheory.ChainFr.IsVacF ψ θ A B f₀ ∧ f₀ ≠ 0 := by
  intro D V W A B θ ψ hψ hθ f hf hf0
  by_contra hno
  push_neg at hno
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have i6 : BorelSpace (WO V W) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO V W) (ratL W V) K hK hKc).1
  obtain ⟨U, -, -, hd⟩ := _root_.GlobalTheory.FockDensity.fockDense D V W A B θ ψ hψ hθ μ 𝓕 ⟨hμ, h𝓕, h1⟩ f hf
  have hspan : fockSpan ψ θ A B U = ⊥ := by
    unfold fockSpan
    rw [Submodule.span_eq_bot]
    rintro g ⟨f₀, P, hv, -, rfl⟩
    rw [hno f₀ hv]
    exact ptF_zero ψ θ A B P
  have hl : l2O μ 𝓕 f = 0 := by
    by_contra hne
    obtain ⟨g, hg, -, hlt⟩ := hd 0 (l2O μ 𝓕 f) (pos_iff_ne_zero.2 hne)
    rw [hspan, Submodule.mem_bot] at hg
    rw [hg, sub_zero] at hlt
    have e : sobO ψ θ μ 𝓕 0 f = l2O μ 𝓕 f := wordSum_zero _ _ _
    rw [e] at hlt
    exact lt_irrefl _ hlt
  have h0 : ∀ᵐ x ∂μ.restrict 𝓕, f x = 0 :=
    (eLpNorm_eq_zero_iff two_ne_zero).1 hl
  exact hf0 (GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL W V) μ 𝓕 h𝓕 f hf.cont
    (GlobalTheory.WeilVacMove.norm_periodic hψ hf) h0)

end GlobalTheory.Mem.VacReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroRationalLiftMemBasePart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.RatLift

theorem exists_rat_lift_mem_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≠ ⊥ → ∃ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p ∧ x ≠ 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ hP hH _ _ p _ i hB
  have hRw := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hk : (R.toCx3 F).KForm false := hRw.kForm
  have he : (R.toCx3 F).EWnorm false := hRw.ewNorm
  have hn : 0 < (R.toCx3 F).nP false := hRw.h4pos.2.2 false
  have h5 : (R.toCx3 F).H5 F.cr false := hRw.lifts0.1
  have hr : (R.toCx3 F).RATth F.cr false := hRw.ratTh
  have h3W : (R.toCx3 F).H3W F.cr false := hRw.liftHyp0.h3W
  have ht : (lv (F.fc (R.toCx3 F).zs) false).Types := hRw.types0
  have hK : ∀ y, y ∈ ⨆ q, (R.toCx3 F).WpK false i q := fun y => CxData.liftsK ht hk he hn h5 hr h3W i y
  have hc0 : cpt A3.A.v0.embedding (0 : Fin ((R.toCx3 F).dW false i) → D.what₂.LL) = 0 := by
    funext l; simp [cpt]
  have hWpK : (R.toCx3 F).WpK false i p ≠ ⊥ := by
    intro h0
    apply hB
    rw [eq_bot_iff]
    intro w hw
    let M : Submodule ℂ ((R.toCx3 F).W i) :=
      ⨆ q, ⨆ (_ : q ≠ p), (R.toCx3 F).Wp i q ⊓ LinearMap.range ((R.toCx3 F).w0C false i)
    have hrat : ∀ y, (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) ∈ M := by
      intro y
      refine Submodule.iSup_induction _ (motive := fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) ∈ M)
        (hK y) ?_ ?_ ?_
      · intro q z hz
        by_cases hq : q = p
        · subst hq
          rw [h0] at hz
          rw [(Submodule.mem_bot _).1 hz, hc0, map_zero]
          exact M.zero_mem
        · exact (le_iSup₂ (f := fun q (_ : q ≠ p) => (R.toCx3 F).Wp i q ⊓ LinearMap.range ((R.toCx3 F).w0C false i)) q hq)
            ⟨hz, ⟨_, rfl⟩⟩
      · rw [hc0, map_zero]
        exact M.zero_mem
      · intro a c ha hc
        have : cpt A3.A.v0.embedding (a + c) = cpt A3.A.v0.embedding a + cpt A3.A.v0.embedding c := by
          funext l; simp [cpt]
        rw [this, map_add (f := _)]
        exact M.add_mem ha hc
    have hrange : LinearMap.range ((R.toCx3 F).w0C false i) ≤ M := by
      rw [LinearMap.range_eq_map, ← (Pi.basisFun ℂ (Fin ((R.toCx3 F).dW false i))).span_eq, Submodule.map_span,
        Submodule.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      have : (Pi.basisFun ℂ (Fin ((R.toCx3 F).dW false i)) k) =
          cpt A3.A.v0.embedding (Pi.single k (1 : D.what₂.LL)) := by
        funext l
        simp only [Pi.basisFun_apply, cpt, Pi.single_apply]
        split_ifs <;> simp
      rw [this]
      exact hrat _
    have hperp : M ≤ (ℂ ∙ w)ᗮ := by
      refine iSup₂_le fun q hq => ?_
      intro v hv
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact (hH.prim.sumW i).1 p q (Ne.symm hq) w hw v hv
    have hww := hperp (hrange hw.2)
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hww
    exact (Submodule.mem_bot ℂ).2 (inner_self_eq_zero.1 hww)
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWpK
  obtain ⟨x, rfl⟩ := ((R.toCx3 F).liftMat_bij F.cr false hk he hn h5 hr i A3.A.μ0).2 y
  refine ⟨x, ?_, ?_⟩
  · have hy' : (R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding
        ((R.toCx3 F).liftMat F.cr false i A3.A.μ0 *ᵥ x)) ∈ (R.toCx3 F).Wp i p := hy
    rw [(R.toCx3 F).key_lift F.cr false h5 hr i A3.A.μ0 x] at hy'
    exact hy'
  · rintro rfl
    exact hy0 (Matrix.mulVec_zero _)

end GlobalTheory.RatLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRankOneIsAvg
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem eq_zero_of_sum_coef {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx n → (H →L[ℂ] H)} {d : ℝ} (hd : IsFdeg (muG ε) σ d) {m : ℕ} {a y : Fin m → H} (ha : Orthonormal ℂ a)
    (h0 : ∀ g ∈ UJset ε, ∑ j, ⟪y j, σ g (a j)⟫_ℂ = 0) (k : Fin m) : y k = 0 := by
  have h1 : ∫ g, ∑ j, coefOn σ (a j) (y j) g * star (coefOn σ (a k) (y k) g) ∂(muG ε) = 0 := by
    have : ∀ g : UJ ε, ∑ j, coefOn σ (a j) (y j) g * star (coefOn σ (a k) (y k) g) = 0 := fun g => by
      rw [← Finset.sum_mul]
      have := h0 (umat g) g.2
      simp only [coefOn]
      rw [this, zero_mul]
    simp only [this, integral_zero]
  rw [integral_finsetSum _ fun j _ => (hd.2 _ _ _ _).1] at h1
  simp only [fun j => (hd.2 (a j) (y j) (a k) (y k)).2, orthonormal_iff_ite.1 ha, ite_mul, ite_div, one_mul, zero_mul,
    zero_div, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  have hd' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  exact inner_self_eq_zero.1 ((div_eq_zero_iff.1 h1).resolve_right hd')

theorem exists_rank_one_isAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ a c : H, a ≠ 0 ∧ c ≠ 0 ∧ IsKFin ε σ a ∧ IsKFin ε σ c ∧ IsAvg ε σ (fun w => ⟪c, w⟫_ℂ • a) := by
  intro n ε H _ _ _ σ h
  obtain ⟨hσ, -, -, ⟨d, hd⟩, b, hb, hb0⟩ := id h
  obtain ⟨A1, A2, A3, A4, A5⟩ := isAvg_closure n ε H σ hσ
  obtain ⟨B1, B2, -, -⟩ := kCoef_kAvg n ε H σ hσ
  have he := B1 b hb
  obtain ⟨m, a, c, ha, haK, hcK, hQ⟩ := _root_.GlobalTheory.TypeSum.kAvg_finite_rank n ε H σ h _ he
  have hQavg := A4 _ (by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1)
  have hc : ∃ k, c k ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply B2 b hb0
    rw [hQ]; simp [hc]
  obtain ⟨k, hk⟩ := hc
  let V : Submodule ℂ (Fin m × Fin m → ℂ) :=
    Submodule.span ℂ ((fun g (p : Fin m × Fin m) => ⟪c p.1, σ g (a p.2)⟫_ℂ) '' UJset ε)
  have hV : ∀ M ∈ V, IsAvg ε σ (fun w => ∑ i, ∑ j, (M (i, j) * ⟪c j, w⟫_ℂ) • a i) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, hg, rfl⟩ := hM
      have := (A2 _ _ hQavg (A2 _ _ (A1 g hg) hQavg).2).2
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hQ, map_sum, map_smul, inner_sum, inner_smul_right, Finset.sum_smul] at this
      simpa only [mul_comm] using this
    | zero => simpa using A5
    | add M N _ _ hM hN =>
      simpa only [Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib] using (A2 _ _ hM hN).1
    | smul t M _ hM =>
      simpa only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, mul_assoc] using A3 t _ hM
  have hN : (fun p : Fin m × Fin m => if p.2 = k then ⟪c p.1, c k⟫_ℂ else 0) ∈ V := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have e : ∀ z : Fin m → H, φ (fun p => ⟪c p.1, z p.2⟫_ℂ) =
        ∑ j, ⟪∑ i, star (φ fun q => if (i, j) = q then 1 else 0) • c i, z j⟫_ℂ := fun z => by
      rw [LinearMap.pi_apply_eq_sum_univ, Fintype.sum_prod_type, Finset.sum_comm]
      simp [sum_inner, inner_smul_left, mul_comm]
    have hy := eq_zero_of_sum_coef hd ha (y := fun j => ∑ i, star (φ fun q => if (i, j) = q then 1 else 0) • c i)
      (fun g hg => by rw [← e fun j => σ g (a j)]; exact hφ _ (Submodule.subset_span ⟨g, hg, rfl⟩))
    have := e fun j => if j = k then c k else 0
    simp only [hy, inner_zero_left, Finset.sum_const_zero] at this
    refine Eq.trans (congrArg φ ?_) this
    funext p
    by_cases hp : p.2 = k <;> simp [hp]
  refine ⟨∑ i, ⟪c i, c k⟫_ℂ • a i, c k, fun h0 => hk ?_, hk,
    (kfin ε σ).sum_mem fun i _ => (kfin ε σ).smul_mem _ (haK i), hcK k, ?_⟩
  · have := ha.inner_right_fintype (fun i => ⟪c i, c k⟫_ℂ) k
    rw [h0, inner_zero_right] at this
    exact inner_self_eq_zero.1 this.symm
  · have := hV _ hN
    simp only [ite_mul, zero_mul, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    simpa only [Finset.smul_sum, smul_smul, mul_comm] using this

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedCartierDivisorOfSncClosedStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduced_cartierDivisor_of_snc_closed : ∀ (X Y : Scheme.{0}) [IsIntegral Y] (j : Y ⟶ X) [IsOpenImmersion j] (T : TopologicalSpace.Closeds X), ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) → j (genericPoint Y) ∉ T → ∃ D : CartierDiv Y, D.Eff ∧ (∀ y, y ∈ D.supp ↔ j y ∈ T) ∧ ∀ (y : Y) (g : Y.functionFieldˣ), D.IsEqn y g → ∀ (f : Y.functionField) (n : ℕ), RegAt y f → RegAt y (f ^ n / g) → RegAt y (f / g) := by
  first | exact @GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv | exact GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv | (intros; apply GlobalTheory.BoundaryDivisor.exists_reduced_cartierDiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerMaps
section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN

theorem exists_teichmuller_maps : ∀ (g : ℕ) (hg : g.Prime), (∃ τ : Fb g hg →* ℂ, ∀ x y, x ≠ 0 → y ≠ 0 → τ x = τ y → x = y) ∧ ∀ (l : ℕ) (hl : l.Prime), ∃ ι : Fb g hg →* Fb l hl, ∀ x y, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime l → (orderOf y).Coprime l → ι x = ι y → x = y :=
  fun g hg => ⟨@GaloisStage.exists_teichC g ⟨hg⟩, fun l hl => @GaloisStage.exists_iota g l ⟨hg⟩ ⟨hl⟩⟩

end GlobalTheory.MemN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueProjectiveBundleFlagRefinementStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_projectiveBundle_flagRefinement : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (ι : Type) [Finite ι] (m k k' : ι → ℕ) (S : Fr M m k) (S' : Fr M' m k') (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω) (EE : M.Lat (Rest m k τ)) (s : Rest m k τ → Ω'), k' τ = k τ + 1 → (∀ τ', τ' ≠ τ → k' τ' = k τ') → A₀ ∈ S.S (genericPoint M.Z) → (∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧ EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A))) → ProjPoints M EE M' φ f s → (∀ z', S'.S z' = stepSet S τ hk A₀ M' φ f s z') → ∀ (K : Type) [Field K] (x : Sp K ⟶ M.Z), ∀ A ∈ S.S (x (IsLocalRing.closedPoint K)), ∀ h : Mat m K, Par k ⊤ h → ∃! p : Sp K ⟶ M'.Z, p ≫ f = x ∧ Bears S' φ A h p := by
  first | exact @GlobalTheory.FlagBundle.StepLift.existsUnique_bears | exact GlobalTheory.FlagBundle.StepLift.existsUnique_bears | (intros; apply GlobalTheory.FlagBundle.StepLift.existsUnique_bears <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModelStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variety_flagRefinementBundle_of_goodModel : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) (ι : Type) (m k : ι → ℕ) (S : Fr M m k), Good M d → ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m k), Y.dim = d ∧ Refines S S' φ f := by
  first | exact @GlobalTheory.FlagBundle.exists_var_refines | exact GlobalTheory.FlagBundle.exists_var_refines | (intros; apply GlobalTheory.FlagBundle.exists_var_refines <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteImageOfIsOpenStabilizerStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_image_of_isOpen_stabilizer_alt : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V), IsOpen {g : G | ρ g v = v} → ∀ S : Set G, IsCompact S → ((fun g => ρ g v) '' S).Finite := by
  first | exact @GlobalTheory.finite_image_of_isOpen_stabilizer | exact GlobalTheory.finite_image_of_isOpen_stabilizer | (intros; apply GlobalTheory.finite_image_of_isOpen_stabilizer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankCoefficientSpaceEqProdRealModels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.CoefDim


open Classical in
theorem finrank_piTensorProduct {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    [∀ i, FiniteDimensional ℂ (E i)] : Module.finrank ℂ (⨂[ℂ] i, E i) = ∏ i, Module.finrank ℂ (E i) := by
  let b := Basis.piTensorProduct (fun i => Module.finBasis ℂ (E i))
  rw [Module.finrank_eq_card_basis b, Fintype.card_pi]
  simp [Fintype.card_fin]

theorem finrank_coef_eq_prod : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Module.finrank ℂ R.cX.W = ∏ τ, Module.finrank ℂ (R.MX.H τ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB
  have hp := GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) R.MX
  have hb := GlobalTheory.DefiniteMult.pair_bijective hB.models.inf hp hB.models.cX hB.models.prX
  have m := GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible D _ _ R.MX hp
  haveI : ∀ τ, FiniteDimensional ℂ (R.MX.H τ) := fun τ => (m τ).1
  haveI : ∀ τ, FiniteDimensional ℂ (R.MX.sm τ) := fun τ => inferInstance
  have hsm : ∀ τ, Module.finrank ℂ (R.MX.sm τ) = Module.finrank ℂ (R.MX.H τ) := fun τ => by
    rw [(m τ).2.1, finrank_top]
  have e : R.cX.W ≃ₗ[ℂ] Module.Dual ℂ (SmT R.MX) := LinearEquiv.ofBijective R.prX hb
  have hT : Module.finrank ℂ (SmT R.MX) = ∏ τ, Module.finrank ℂ (R.MX.H τ) :=
    (finrank_piTensorProduct (fun τ => R.MX.sm τ)).trans (Finset.prod_congr rfl fun τ _ => hsm τ)
  haveI : FiniteDimensional ℂ (SmT R.MX) :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun τ => Module.finBasis ℂ (R.MX.sm τ)))
  rw [e.finrank_eq, Subspace.dual_finrank_eq, hT]

end GlobalTheory.CoefDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLab
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.HasLabelling

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

def HasLab (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (σ : D.what₂.FT) (p : A3.fam3.base3.Ix) : Prop :=
  (∀ i : Fin D.R.m, (D.what₂.isot ((i : ℕ) + 1) σ).map (Y.mj.eW i) ≤ R.Wp3 i p) ∧
  ∀ k, D.what₂.ft0 k = σ → ∃ x ∈ R.EEp3 p,
    ((Y.Iz.jE (D.what₂.onb0 k)).1 : (toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop).Amb 0) = PiTensorProduct.lift (R.HE.e x)

end GlobalTheory.Mem.R3.HasLabelling
end

