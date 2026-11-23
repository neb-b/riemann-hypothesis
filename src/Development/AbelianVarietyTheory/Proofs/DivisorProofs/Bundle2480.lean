module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0465
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0632
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsStableBasOfPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2401
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialPrimitiveU
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem symTup_unit_of_prim : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsIntegrallyClosed V] [Field K] (io : FractionRing V →+* K) (N : ℕ) (c : Fin N → K) (e : Fin N → FractionRing V), Prim (io.comp (algebraMap V (FractionRing V))) c → (∀ j, io (e j) = symTup c j) → ∃ e' : Fin N → V, (∀ j, algebraMap V (FractionRing V) (e' j) = e j) ∧ ∃ j, IsUnit (e' j) := by
  intro V K _ _ _ _ _ io N c e hP he
  set i := io.comp (algebraMap V (FractionRing V)) with hi
  have hio : Function.Injective io := io.injective
  have hinj : Function.Injective i := hio.comp (IsFractionRing.injective V (FractionRing V))
  letI : Algebra V K := i.toAlgebra
  have hcI : ∀ a, IsIntegral V (c a) := hP.1
  have hsI : ∀ j, IsIntegral V (symTup c j) := by
    intro j
    have : symTup c j ∈ integralClosure V K := by
      unfold symTup
      refine Subalgebra.pow_mem _ ?_ _
      rw [Finset.esymm_map_val]
      exact Subalgebra.sum_mem _ fun t _ => Subalgebra.prod_mem _ fun b _ => hcI b
    exact this
  let φ : FractionRing V →ₐ[V] K := { io with commutes' := fun r => rfl }
  have heI : ∀ j, IsIntegral V (e j) := fun j =>
    (isIntegral_algHom_iff φ hio).1 (by rw [show φ (e j) = io (e j) from rfl, he j]; exact hsI j)
  choose e' he' using fun j => IsIntegrallyClosed.isIntegral_iff.1 (heI j)
  refine ⟨e', he', ?_⟩
  obtain ⟨a₀, hc0, hinv⟩ := hP.2
  obtain ⟨W, hle⟩ := (LocalSubring.range i).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.1 hle
  have memW : ∀ x : K, i.IsIntegralElem x → x ∈ W := by
    intro x ⟨p, hp, hx⟩
    have : IsIntegral W x := by
      let g : V →+* W := i.codRestrict W (fun v => hle ⟨v, rfl⟩)
      refine ⟨p.map g, hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]; exact hx
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    rw [← hy]; exact y.2
  have hcW : ∀ a, c a ∈ W := fun a => memW _ (hP.1 a)
  have hc0W : (c a₀)⁻¹ ∈ W := memW _ hinv
  let y : Fin N → W := fun a => ⟨c a * (c a₀)⁻¹, mul_mem (hcW a) hc0W⟩
  have hy0 : y a₀ = 1 := Subtype.ext (mul_inv_cancel₀ hc0)
  obtain ⟨k, hk1, hkN, hu⟩ := GlobalTheory.exists_isUnit_esymm_of_eq_one W (Fin N) y a₀ hy0
  rw [Fintype.card_fin] at hkN
  set E := (Finset.univ.val.map y).esymm k with hE
  let u0 : W := ⟨c a₀, hcW a₀⟩
  have hu0 : IsUnit u0 := isUnit_iff_exists_inv.2 ⟨⟨(c a₀)⁻¹, hc0W⟩, Subtype.ext (mul_inv_cancel₀ hc0)⟩
  let Z : W := (u0 ^ k * E) ^ (N.factorial / k)
  have hZ : IsUnit Z := ((hu0.pow k).mul hu).pow _
  let j : Fin N := ⟨k - 1, by omega⟩
  have hjk : (j : ℕ) + 1 = k := by simp only [j]; omega
  have hZj : (Z : K) = i (e' j) := by
    have : i (e' j) = io (e j) := by rw [hi, RingHom.comp_apply, he' j]
    rw [this, he j]
    simp only [Z, symTup, hjk, hE, Finset.esymm_map_val]
    push_cast
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(Finset.mem_powersetCard.1 ht).2.symm, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [y, u0]
    field_simp
  refine ⟨j, ?_⟩
  have hmem : i (e' j) ∈ (LocalSubring.range i).toSubring := ⟨e' j, rfl⟩
  have h1 : IsUnit (Subring.inclusion hle ⟨i (e' j), hmem⟩) := by
    have h0 : Subring.inclusion hle ⟨i (e' j), hmem⟩ = Z := by apply Subtype.ext; exact hZj.symm
    rw [h0]; exact hZ
  obtain ⟨u, hu'⟩ := hloc.map_nonunit _ h1
  obtain ⟨w, hw⟩ := ((u⁻¹ : Units _) : (LocalSubring.range i).toSubring).2
  refine isUnit_iff_exists_inv.2 ⟨w, hinj ?_⟩
  have h3 : ((u : (LocalSubring.range i).toSubring) : K) * (((u⁻¹ : Units _) : (LocalSubring.range i).toSubring) : K) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  rw [map_mul, map_one, hw, ← h3, hu']

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialScaledFini
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

open Polynomial

private theorem symTup_mul_left {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (a : R) (j : Fin N) :
    symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j := by
  have h : (Finset.univ.val.map fun b => a * c b) = (Finset.univ.val.map c).map (fun x => a • x) := by
    rw [Multiset.map_map]; rfl
  have hd : ((j : ℕ) + 1) ∣ N.factorial := Nat.dvd_factorial (Nat.succ_pos _) j.isLt
  unfold symTup
  rw [h, ← Multiset.pow_smul_esymm, smul_eq_mul, mul_pow, ← pow_mul, Nat.mul_div_cancel' hd]

theorem symTup_eq_finite (K : Type) [Field K] (N : ℕ) (e : Fin N → K) :
    {c : Fin N → K | symTup c = e}.Finite := by
  classical

  let A : Fin (N + 1) → Set K := fun k =>
    {x | ((k : ℕ) = 0 → x = 1) ∧ ∀ j : Fin N, (j : ℕ) + 1 = k → x ^ (N.factorial / ((j : ℕ) + 1)) = e j}
  have hA : ∀ k, (A k).Finite := by
    intro k
    by_cases hk : (k : ℕ) = 0
    · exact (Set.finite_singleton (1 : K)).subset fun x hx => hx.1 hk
    · have hk1 : (k : ℕ) - 1 < N := by omega
      let j : Fin N := ⟨(k : ℕ) - 1, hk1⟩
      have hj : (j : ℕ) + 1 = k := by simp [j]; omega
      have hpos : 0 < N.factorial / ((j : ℕ) + 1) :=
        Nat.div_pos ((Nat.succ_le_of_lt j.isLt).trans (Nat.self_le_factorial N)) (Nat.succ_pos _)
      refine (Polynomial.finite_setOf_isRoot (X_pow_sub_C_ne_zero hpos (e j))).subset ?_
      intro x hx
      simp [IsRoot, hx.2 j hj]
  let V : Set (Fin (N + 1) → K) := Set.pi Set.univ A
  have hV : V.Finite := Set.Finite.pi hA
  let poly : (Fin (N + 1) → K) → K[X] := fun s =>
    ∑ k : Fin (N + 1), (-1) ^ (k : ℕ) * (C (s k) * X ^ (N - (k : ℕ)))
  let R : Set K := ⋃ p ∈ poly '' V, {x | x ∈ p.roots}
  have hR : R.Finite := (hV.image poly).biUnion fun p _ => Multiset.finite_toSet p.roots
  refine (Set.Finite.pi (t := fun _ : Fin N => R) fun _ => hR).subset ?_
  intro c hc
  simp only [Set.mem_setOf_eq] at hc
  let m : Multiset K := Finset.univ.val.map c
  have hm : Multiset.card m = N := by simp [m]
  let s : Fin (N + 1) → K := fun k => m.esymm k
  have hs : s ∈ V := by
    intro k _
    refine ⟨fun hk => ?_, fun j hj => ?_⟩
    · simp [s, hk, Multiset.esymm]
    · have := congrFun hc j
      simp only [symTup] at this
      simp only [s, ← hj]
      exact this
  have hpoly : poly s = (m.map fun t => X - C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, hm, Finset.sum_range (fun j => (-1) ^ j * (C (m.esymm j) * X ^ (N - j)))]
  intro a _
  simp only [R, Set.mem_iUnion, Set.mem_image]
  refine ⟨poly s, ⟨s, hs, rfl⟩, ?_⟩
  simp only [Set.mem_setOf_eq, hpoly, Polynomial.roots_multiset_prod_X_sub_C]
  exact Multiset.mem_map_of_mem c (Finset.mem_univ a)

theorem symTup_scale_finite : ∀ (K : Type) [Field K] [IsAlgClosed K] (N : ℕ) (e : Fin N → K), ∃ T : Finset (Fin N → K),
    ∀ (c : Fin N → K) (a : K), a ≠ 0 → (∀ j, symTup c j = a * e j) → ∃ mu : K, mu ≠ 0 ∧ (fun b => mu * c b) ∈ T := by
  intro K _ _ N e
  refine ⟨(symTup_eq_finite K N e).toFinset, ?_⟩
  intro c a ha hc
  obtain ⟨mu, hmu⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ (Nat.factorial_pos N)
  have hmu0 : mu ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.factorial_pos N).ne'] at hmu
    exact inv_ne_zero ha hmu.symm
  refine ⟨mu, hmu0, ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  funext j
  rw [symTup_mul_left, hmu, hc, ← _root_.mul_assoc, inv_mul_cancel₀ ha, _root_.one_mul]

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiesBOfExplicit
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.BasicNotions.TH Formalism.L2.GlobalTheoryTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.PrimIn.AtData


set_option maxHeartbeats 1000000 in
theorem ev_params : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) →
    (∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m → X.toD7.what₂.Aj j w = 0) →
    ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ SizesAt L ∧ Nonempty (ParameterChoice' X.toD7 L) ∧
      8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV := by
  refine ⟨1, one_pos, fun eps C8 h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max x0 x1, ?_⟩
  rintro K rfl rfl rfl hs hx X hO heta hA
  have hP := K.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx) hP.rank hP.val
    (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta (fun u => by
      have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
      rw [e, K.Gam_eq, GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) hA
  obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
    ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
  exact ⟨L, e1, M.sizes, ⟨M.params⟩, M.parT.nV_ge⟩

end GlobalTheory.PrimIn.AtData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToProjSecPullSecPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb.Fib

theorem trait (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (M : Modif R) (x₀ : M.S)
    (hx : M.π x₀ = closedPoint R) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S),
      GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x₀ :=
  _root_.GlobalTheory.Mum.exists_trait_over_closedPoint R hR M x₀ hx

theorem compositum (X : Scheme.{0}) (K₁ K₂ : Type) [Field K₁] [Field K₂] (a : Sp K₁ ⟶ X) (b : Sp K₂ ⟶ X)
    (h : a (closedPoint K₁) = b (closedPoint K₂)) :
    ∃ (Ω : Type) (_ : Field Ω) (i₁ : K₁ →+* Ω) (i₂ : K₂ →+* Ω), spMap i₁ ≫ a = spMap i₂ ≫ b :=
  _root_.GlobalTheory.Mum.exists_common_field_of_point_eq X K₁ K₂ a b h

theorem baseChangeIso (S : Scheme.{0}) (G : Over S) [GrpObj G] (W' : Type) [CommRing W'] [IsLocalRing W']
    (G' : Over (Sp W')) [GrpObj G'] (ξ' : Sp W' ⟶ S) (β : G'.left ⟶ G.left) (hβ : IsGrpPullback G' G ξ' β)
    (k : Type) [Field k] (Y : Over (Sp k)) [GrpObj Y] (κ' : k →+* ResidueField W')
    (e' : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ')).obj Y) (he' : IsMonHom e'.hom)
    (Ω : Type) [Field Ω] (x : Sp Ω ⟶ S) (κ : k →+* Ω) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω')
    (i₂ : ResidueField W' →+* Ω') (hc : spMap io ≫ x = spMap i₂ ≫ spMap (residue W') ≫ ξ')
    (hκ : io.comp κ = i₂.comp κ') :
    ∃ (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y)
      (τ : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ ((Over.pullback (spMap (residue W'))).obj G').left),
      IsMonHom e.hom ∧ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β = pullback.fst G.hom (spMap io ≫ x) ∧
      e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) = τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') :=
  _root_.GlobalTheory.Mum.FibBC.fibre_baseChange S G W' G' ξ' β hβ k Y κ' e' he' Ω x κ Ω' io i₂ hc hκ

theorem toProj_secPull_secPull (R : Type) [CommRing R] (N : ℕ) (X Y Z : Scheme.{0}) (L : LB X)
    (s : Fin (N + 1) → L.Sec) (h : Y ⟶ X) (g : Z ⟶ Y) (f : Z ⟶ Sp R)
    (hs₁ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) = ⊤)
    (hs₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (g ≫ h)) = ⊤) :
    GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) hs₁ =
      GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (s i) (g ≫ h)) hs₂ :=
  _root_.GlobalTheory.Mum.toProj_secPull_secPull R N X Y Z L s h g f hs₁ hs₂

theorem toProj_congr {R : Type} [CommRing R] {N : ℕ} {X Z : Scheme.{0}} {L : LB X} (s : Fin (N + 1) → L.Sec)
    {a b : Z ⟶ X} (hab : a = b) {f g : Z ⟶ Sp R} (hfg : f = g)
    (h₁ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) a) = ⊤) (h₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) b) = ⊤) :
    GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (s i) a) h₁ = GlobalTheory.ProjSpace.toProj g (fun i => GlobalTheory.secPull (s i) b) h₂ := by
  subst hab; subst hfg; rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem fib : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens),
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O →
    (∀ g : G.left, M.π (G.hom g) = closedPoint R → g ∈ GlobalTheory.Mum.SecEmb.embH s) →
    ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ M.S) (κ : ResidueField R →+* Ω), x ≫ M.π = spMap (κ.comp (residue R)) →
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω')
      (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y)
      (l : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ (GlobalTheory.Mum.SecEmb.embH s).toScheme), IsMonHom e.hom ∧
      l ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = pullback.fst G.hom (spMap io ≫ x) ∧
      l ≫ GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s = e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) ≫ j := by
  intro R _ _ _ hR M G _ hG B L hB hL N s θ Y _ hY j hj hji O hT hH Ω _ x κ hx
  have hcl : ∀ q : Sp Ω, M.π (x q) = closedPoint R := fun q => by
    rw [← Scheme.Hom.comp_apply, hx, Subsingleton.elim q (closedPoint Ω)]
    exact IsLocalRing.comap_closedPoint (κ.comp (residue R))
  obtain ⟨W, _, _, _, φ, ξ, hW, hφi, hφl, hξ, hξ0⟩ := trait R hR M _ (hcl (closedPoint Ω))
  obtain ⟨W', _, _, _, io', G', _, β, κ', e', hW', hio', hiof, hβ, hκ', he', hptw⟩ := hT W hW φ ξ hφi hφl hξ
  have hio0 : (spMap io') (closedPoint W') = closedPoint W := by
    letI := io'.toAlgebra
    have : Algebra.IsIntegral W W' := ⟨fun a => hiof.to_isIntegral a⟩
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) hiof.to_isIntegral (maximalIdeal W')))
  have hres0 : (spMap (residue W')) (closedPoint (ResidueField W')) = closedPoint W' :=
    IsLocalRing.comap_closedPoint (residue W')
  have hpt0 : (spMap (residue W') ≫ spMap io' ≫ ξ) (closedPoint (ResidueField W')) = x (closedPoint Ω) := by
    show ξ (spMap io' (spMap (residue W') (closedPoint _))) = _
    rw [hres0, hio0, hξ0]
  obtain ⟨Ω', _, io, i₂, hc⟩ := compositum M.S Ω (ResidueField W') x _ hpt0.symm
  have hκ : io.comp κ = i₂.comp κ' := by
    have e1 : spMap ((io.comp κ).comp (residue R)) = spMap ((i₂.comp κ').comp (residue R)) := by
      rw [RingHom.comp_assoc, spMap_comp', ← hx, RingHom.comp_assoc, hκ', spMap_comp', spMap_comp', spMap_comp',
        ← hξ, ← Category.assoc, hc]
      simp only [Category.assoc]
    have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    ext a
    obtain ⟨r, rfl⟩ := residue_surjective a
    exact congrArg (fun f : R →+* Ω' => f r) e2
  obtain ⟨e, τ, he, hτ, heτ⟩ := baseChangeIso M.S G W' G' (spMap io' ≫ ξ) β hβ (ResidueField R) Y κ' e' he' Ω x κ
    Ω' io i₂ hc hκ
  have hrange : Set.range (pullback.fst G.hom (spMap io ≫ x)) ⊆ Set.range (GlobalTheory.Mum.SecEmb.embH s).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hH
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition_assoc, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    exact hcl _
  let l := IsOpenImmersion.lift (GlobalTheory.Mum.SecEmb.embH s).ι (pullback.fst G.hom (spMap io ≫ x)) hrange
  have hl : l ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = pullback.fst G.hom (spMap io ≫ x) := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Ω', inferInstance, io, e, l, he, hl, ?_⟩
  have : IsReduced ((Over.pullback (spMap (io.comp κ))).obj Y).left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd Y.hom (spMap (io.comp κ)))
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have : IsReduced ((Over.pullback (spMap io ≫ x)).obj G).left := isReduced_of_isOpenImmersion e.hom.left
  have hsep : IsSeparated (PSpace.str R N) := by unfold PSpace.str; infer_instance
  refine GlobalTheory.hom_ext_of_geometricPoints_dense (PSpace.str R N) _ _ ?_ Set.univ dense_univ ?_
  · have a1 : GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s ≫ PSpace.str R N = (GlobalTheory.Mum.SecEmb.embH s).ι ≫ G.hom ≫ M.π :=
      GlobalTheory.ProjSpace.toProj_str _ _ _
    have eo : e.hom.left ≫ pullback.snd Y.hom (spMap (io.comp κ)) = pullback.snd G.hom (spMap io ≫ x) := Over.w e.hom
    have a2 : (l ≫ GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s) ≫ PSpace.str R N =
        pullback.snd G.hom (spMap io ≫ x) ≫ spMap io ≫ x ≫ M.π := by
      rw [Category.assoc, a1, reassoc_of% hl, pullback.condition_assoc, Category.assoc]
    have a3 : (e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) ≫ j) ≫ PSpace.str R N =
        pullback.snd G.hom (spMap io ≫ x) ≫ spMap (io.comp κ) ≫ spMap (residue R) := by
      rw [Category.assoc, Category.assoc, hj, pullback.condition_assoc, reassoc_of% eo]
    rw [a2, a3, hx, spMap_comp', spMap_comp']
    simp only [Category.assoc]
  · intro K _ _ q _
    obtain ⟨⟨hs, hproj⟩, -⟩ := hptw K (q ≫ τ) (q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W')))
      (q ≫ τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ')) (by simp) (by simp)
    have e3 : q ≫ τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') ≫ j =
        (q ≫ τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ')) ≫ j := by simp only [Category.assoc]
    rw [reassoc_of% heτ, e3, ← hproj]
    have hqb : (q ≫ l) ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = (q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ β := by
      rw [Category.assoc, hl, ← hτ]; simp only [Category.assoc]
    have hbase : (q ≫ l) ≫ (GlobalTheory.Mum.SecEmb.embH s).ι ≫ G.hom ≫ M.π =
        (q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ G'.hom ≫ spMap (io'.comp φ) := by
      have hqb' : q ≫ l ≫ (GlobalTheory.Mum.SecEmb.embH s).ι = q ≫ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β := by
        simp only [Category.assoc] at hqb; exact hqb
      rw [Category.assoc q l, reassoc_of% hqb', hβ.1.w_assoc, Category.assoc (spMap io'), hξ, spMap_comp']
      simp only [Category.assoc]
    have hs₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) ((q ≫ l) ≫ (GlobalTheory.Mum.SecEmb.embH s).ι)) = ⊤ := by
      rw [hqb]; exact hs
    rw [← Category.assoc]
    show (q ≫ l) ≫ GlobalTheory.ProjSpace.toProj ((GlobalTheory.Mum.SecEmb.embH s).ι ≫ G.hom ≫ M.π)
      (fun i => GlobalTheory.secPull (s i) (GlobalTheory.Mum.SecEmb.embH s).ι) (GlobalTheory.Mum.SecEmb.iSup_nonzeroLocus_embH s) = _
    rw [← GlobalTheory.ProjSpace.toProj_secPull]
    exact (toProj_secPull_secPull R N _ _ _ B s _ (q ≫ l) _ _ hs₂).trans (toProj_congr s hqb hbase _ _)

end GlobalTheory.Mum.SecEmb.Fib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqDegreeMulStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topSelfIntersection_pullback_eq_degree_mul : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k] (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X ≤ D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ B : LB X, B.IsLB → letI := GlobalTheory.algebraΓOfHom p; letI := GlobalTheory.algebraΓOfHom q; topSelfIntersection k (B.pull π) D = (π.residueDegree (genericPoint Y) : ℤ) * topSelfIntersection k B D := by
  first | exact @GlobalTheory.ProjFormulaTop.topSelf_pull_eq_mul | exact GlobalTheory.ProjFormulaTop.topSelf_pull_eq_mul | (intros; apply GlobalTheory.ProjFormulaTop.topSelf_pull_eq_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitImports
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaMove

variable {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT}
  {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG}

def tf (wA : LB.Iso LA (LP.pull α)) (ℓ : LB.Iso LG (LP.pull β)) (w : LB.Iso LT (LG.pull c)) (f : Y' ⟶ Y)
    (sA : Y ⟶ XA) (sT : Y' ⟶ XT) {Z : Scheme.{0}} (q : Z ⟶ Y') (z : Z) (JP : (Z ⟶ XP) → LP.ι)
    (JA : (Z ⟶ XA) → LA.ι) (JG : (Z ⟶ XG) → LG.ι) (Jt : (Z ⟶ XT) → LT.ι) : (Z.presheaf.stalk z)ˣ :=
  (gw wA (q ≫ f ≫ sA) z (JP (q ≫ sT ≫ c ≫ β)) (JA (q ≫ f ≫ sA)))⁻¹ *
    gw ℓ (q ≫ sT ≫ c) z (JP (q ≫ sT ≫ c ≫ β)) (JG (q ≫ sT ≫ c)) *
    gw w (q ≫ sT) z (JG (q ≫ sT ≫ c)) (Jt (q ≫ sT))

end GlobalTheory.ThetaMove
end
end

