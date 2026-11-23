module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RhoPowLowerBoundSwappedPairs
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

theorem finite_between (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (R : Submodule O A) (hR : R.FG)
    (a : O) (ha : a ≠ 0) : Finite {N : Submodule O A // N ≤ R ∧ ∀ x ∈ R, a • x ∈ N} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := ‹Finite (IsLocalRing.ResidueField O)›
  haveI : Finite (O ⧸ Ideal.span {a}) := by
    rw [Ideal.span_singleton_eq_span_singleton.2 hk, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq]
    exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k
  haveI : Module.Finite O R := Module.Finite.iff_fg.2 hR
  set J : Submodule O R := Ideal.span {a} • (⊤ : Submodule O R) with hJ
  haveI hQ : Finite (R ⧸ J) := Submodule.finite_quotient_smul (Ideal.span {a}) (N := ⊤) Module.Finite.fg_top
  have hJle : ∀ N : {N : Submodule O A // N ≤ R ∧ ∀ x ∈ R, a • x ∈ N}, J ≤ N.1.comap R.subtype := by
    intro N x hx
    rw [hJ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, -, rfl⟩ := hx
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_smul]
    exact N.2.2 _ y.2
  let φ : {N : Submodule O A // N ≤ R ∧ ∀ x ∈ R, a • x ∈ N} → Set (R ⧸ J) := fun N =>
    ((N.1.comap R.subtype).map J.mkQ : Set (R ⧸ J))
  refine Finite.of_injective φ ?_
  intro N N' h
  have h1 : (N.1.comap R.subtype).map J.mkQ = (N'.1.comap R.subtype).map J.mkQ := SetLike.coe_injective h
  have h2 := congrArg (Submodule.comap J.mkQ) h1
  rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ, sup_eq_right.2 (hJle N),
    sup_eq_right.2 (hJle N')] at h2
  have h3 := congrArg (Submodule.map R.subtype) h2
  rw [Submodule.map_comap_eq, Submodule.map_comap_eq, Submodule.range_subtype,
    inf_eq_right.2 N.2.1, inf_eq_right.2 N'.2.1] at h3
  exact Subtype.ext h3

theorem isIntegral_sigma (K : UQ) (B : InvAlg K) (y : B.A) (hy : IsIntegral K.O y) : IsIntegral K.O (B.σ y) := by
  obtain ⟨p, hpm, hp⟩ := hy
  choose cO hcO using K.c_int
  have hinj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E
  let ψ : K.O →+* K.O :=
    { toFun := cO
      map_one' := hinj (by rw [← hcO, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [← hcO, map_mul, map_mul, map_mul, hcO, hcO])
      map_zero' := hinj (by rw [← hcO, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [← hcO, map_add (f := _), map_add (f := _), map_add (f := _), hcO, hcO]) }
  have hcomp : (algebraMap K.O B.A).comp ψ = (B.σ : B.A →+* B.A).comp (algebraMap K.O B.A) := by
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg]
    show _ = algebraMap K.E B.A (K.c (algebraMap K.O K.E x))
    rw [hcO]; rfl
  refine ⟨p.map ψ, hpm.map ψ, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]
  have := Polynomial.hom_eval₂ p (algebraMap K.O B.A) (B.σ : B.A →+* B.A) y
  exact this.symm.trans (by rw [hp, map_zero])

theorem finite_rhoSet (K : UQ) (B : InvAlg K) (hsep : B.P.Separable) (a : K.O) (ha : K.Small a) (k : ℕ) :
    Finite {c : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
      IsIntegral K.O ((((Quotient.out c : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} := by
  classical
  set R : Submodule K.O B.A := (integralClosure K.O B.A).toSubmodule with hR
  have hRfg : R.FG := by
    have := _root_.GlobalTheory.UnitLemma.IntegralFinite.finite_integralClosure K B hsep
    have h2 := Module.Finite.fg_top (R := K.O) (M := integralClosure K.O B.A)
    have h3 := h2.map (integralClosure K.O B.A).val.toLinearMap
    convert h3 using 1
    ext x; simp [hR]
  have ha0 : a ^ (2 * k) ≠ 0 := pow_ne_zero _ ha.1
  have hfin := finite_between K.O B.A R hRfg (a ^ (2 * k)) ha0
  have hσα : B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A a := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ha.2.2]
  have hαu : IsUnit (algebraMap K.O B.A a) := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    intro h0
    exact ha.1 ((injective_iff_map_eq_zero (algebraMap K.O K.E)).1 (IsFractionRing.injective K.O K.E) a h0)
  set αu : B.Aˣ := hαu.unit with hαudef
  have hαeq : (αu : B.A) = algebraMap K.O B.A a := hαu.unit_spec
  have hmem : ∀ (u : B.A) (y : B.A), y ∈ mulLat K.O u R ↔ ∃ r ∈ R, u * r = y := by
    intro u y
    simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]

  have hσinv : ∀ t : B.T, B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) = ((t : B.Aˣ) : B.A) := by
    intro t
    have ht : ((t : B.Aˣ) : B.A) * B.σ ((t : B.Aˣ) : B.A) = 1 := t.2
    have h1 : B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) * B.σ ((t : B.Aˣ) : B.A) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A)
        = B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) * (((t : B.Aˣ) : B.A) * B.σ ((t : B.Aˣ) : B.A)) := by rw [ht, mul_one]
      _ = ((t : B.Aˣ) : B.A) * (B.σ ((((t : B.Aˣ)⁻¹ : B.Aˣ)) : B.A) * B.σ ((t : B.Aˣ) : B.A)) := by ring
      _ = ((t : B.Aˣ) : B.A) := by rw [h1, mul_one]
  let φ : {c : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
      IsIntegral K.O ((((Quotient.out c : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} →
      {N : Submodule K.O B.A // N ≤ R ∧ ∀ x ∈ R, a ^ (2 * k) • x ∈ N} := fun c =>
    ⟨mulLat K.O ((((Quotient.out c.1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A) R, by
      intro y hy
      obtain ⟨r, hr, rfl⟩ := (hmem _ _).1 hy
      exact c.2.mul hr, by
      intro x hx
      set t : B.T := Quotient.out c.1
      have h2 : IsIntegral K.O (((t : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) := by
        have := isIntegral_sigma K B _ c.2
        rwa [map_mul, map_pow, hσα, hσinv] at this
      refine (hmem _ _).2 ⟨((t : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k * x, h2.mul hx, ?_⟩
      rw [Algebra.smul_def, map_pow, pow_mul]
      have : (((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * ((t : B.Aˣ) : B.A) = 1 := Units.inv_mul _
      linear_combination (algebraMap K.O B.A a ^ k * algebraMap K.O B.A a ^ k * x) * this⟩
  refine Finite.of_injective φ ?_
  rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
  have hN := congrArg Subtype.val h
  simp only [φ] at hN
  set t : B.T := Quotient.out c with htdef
  set t' : B.T := Quotient.out c' with ht'def
  have h1R : (1 : B.A) ∈ R := (integralClosure K.O B.A).one_mem

  have key : ∀ (s s' : B.T), mulLat K.O ((((s : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) R =
      mulLat K.O ((((s' : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) R →
      IsIntegral K.O ((((s : B.Aˣ)⁻¹ * (s' : B.Aˣ) : B.Aˣ)) : B.A) := by
    intro s s' hss
    have : (((s : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k ∈
        mulLat K.O ((((s' : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) R := by
      rw [← hss]; exact (hmem _ _).2 ⟨1, h1R, mul_one _⟩
    obtain ⟨r, hr, hr'⟩ := (hmem _ _).1 this
    have h1 : ((s' : B.Aˣ) : B.A) * (((s' : B.Aˣ)⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv _
    have h2 : algebraMap K.O B.A a ^ k * (((αu ^ k)⁻¹ : B.Aˣ) : B.A) = 1 := by
      rw [← hαeq, ← Units.val_pow_eq_pow_val, Units.mul_inv]
    have : ((((s : B.Aˣ)⁻¹ * (s' : B.Aˣ) : B.Aˣ)) : B.A) = r := by
      rw [Units.val_mul]
      linear_combination -(((s' : B.Aˣ) : B.A) * (((αu ^ k)⁻¹ : B.Aˣ) : B.A) * hr' - r * algebraMap K.O B.A a ^ k * (((αu ^ k)⁻¹ : B.Aˣ) : B.A) * h1 - r * h2 + (((s : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * ((s' : B.Aˣ) : B.A) * h2)
    rw [this]; exact hr
  have hA := key t t' hN
  have hB := key t' t hN.symm
  have hmemU : (t : B.Aˣ)⁻¹ * (t' : B.Aˣ) ∈ intUnits K.O B.A := by
    refine ⟨hA, ?_⟩
    have : ((t : B.Aˣ)⁻¹ * (t' : B.Aˣ))⁻¹ = ((t' : B.Aˣ)⁻¹ * (t : B.Aˣ)) := by
      rw [mul_inv_rev, inv_inv]
    rw [this]; exact hB
  have : c = c' := by
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hmemU
  subst this
  rfl

theorem rho_lower : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ k : ℕ, (k + 1) ^ (Fintype.card ι - S.card) ≤ B.rho (algebraMap K.O B.A a ^ k) := by
  intro K B ι _ e π S a hsep ha hF k
  classical
  have hfin := finite_rhoSet K B hsep a ha k
  obtain ⟨f, hf, hint⟩ := _root_.GlobalTheory.UnitLemma.TorusPts.torus_points K B ι e S a ha hF.1 k
  let g : ({i // i ∉ S} → Fin (k + 1)) → {c : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
      IsIntegral K.O ((((Quotient.out c : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} :=
    fun n => ⟨f n, hint n⟩
  have hg : Function.Injective g := fun n n' h => hf (congrArg Subtype.val h)
  have h := Nat.card_le_card_of_injective g hg
  unfold InvAlg.rho
  refine le_trans (le_of_eq ?_) h
  rw [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_coe]

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureEtaleHermitianEqCoords
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def ccLin (A : Et F E) (e : A.L) : (A.K × A.K) →ₗ[F] A.L where
  toFun := cc A e
  map_add' p q := by simp only [cc, Prod.fst_add, Prod.snd_add, map_add (f := _)]; ring
  map_smul' c p := by
    simp only [cc, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
    simp only [Algebra.smul_def, IsScalarTower.algebraMap_apply F A.K A.L, map_mul]
    ring

def ccEquiv [Unram F E] (A : Et F E) (e : A.L) (h1 : ∀ p, ci A e (cc A e p) = p)
    (h2 : ∀ y, cc A e (ci A e y) = y) : (A.K × A.K) ≃L[F] A.L :=
  haveI := EtMeas.finite_L A
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  let l : (A.K × A.K) ≃ₗ[F] A.L := { ccLin A e with invFun := ci A e, left_inv := h1, right_inv := h2 }
  { l with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap l.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap l.symm.toLinearMap }

def tt (A : Et F E) (ν : Measure A.K) (ψ : AddChar F ℂ) (x : A.K) (Φ : A.K × A.K → ℂ) : A.K × A.K → ℂ :=
  pt A ν ψ x (fun q => pt A ν ψ x Φ (q.2, q.1))

theorem measure_eq_coords : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (e : A.L), e * e = e → star e = 1 - e → ∀ (ν : Measure A.K) (μ : Measure A.L), SelfDual ν (Hyp.kx A ψ x) → SelfDual μ (A.kerL ψ x) → ∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν := by
  intro F E _ _ _ _ _ A ψ hψ x e he hse ν μ hν hμ h hh
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : IsUltrametricDist F := Unram.ultraF E
  haveI := EtMeas.finite_L A
  haveI := GlobalTheory.FourKFub.secondCountableK A
  obtain ⟨_, _, _, _, hS⟩ := EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨h1, h2, -, hker, -⟩ := _root_.GlobalTheory.JR.Hyp.coord_structure F E A e he hse
  obtain ⟨htc, htc'⟩ := _root_.GlobalTheory.JR.Hyp.isTest_coord F E A e h1 h2
  have hlc := (GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel F E A ψ hψ).2 (x : A.K)
  haveI : ν.IsAddHaarMeasure := hν.1
  let C := ccEquiv A e h1 h2
  have hC : (C : A.K × A.K → A.L) = cc A e := rfl
  set μ₀ := Measure.map (cc A e) (ν.prod ν) with hμ₀
  haveI : μ₀.IsAddHaarMeasure := by rw [hμ₀, ← hC]; exact C.isAddHaarMeasure_map _
  have hint : ∀ g : A.L → ℂ, IsTest g → ∫ y, g y ∂μ₀ = ∫ a, ∫ b, g (cc A e (a, b)) ∂ν ∂ν := by
    intro g hg
    have e1 : ∫ y, g y ∂μ₀ = ∫ p, g (cc A e p) ∂(ν.prod ν) := C.toHomeomorph.measurableEmbedding.integral_map g
    rw [e1]
    exact integral_prod _ (((htc g hg).1.continuous).integrable_of_hasCompactSupport (htc g hg).2)
  have hsw : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun q : A.K × A.K => Φ (q.2, q.1)) := fun Φ hΦ =>
    ⟨hΦ.1.comp_continuous continuous_swap, hΦ.2.comp_homeomorph (Homeomorph.prodComm A.K A.K)⟩
  have hpt : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (pt A ν ψ x Φ) := fun Φ hΦ =>
    _root_.GlobalTheory.JR.Hyp.pt_isTest F E A ψ hψ x ν hν.1 Φ hΦ
  have hT : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (tt A ν ψ x Φ) := fun Φ hΦ =>
    hpt _ (hsw _ (hpt Φ hΦ))
  have hTT : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → tt A ν ψ x (tt A ν ψ x Φ) = fun p => Φ (-p.1, -p.2) := by
    intro Φ hΦ
    have i1 := _root_.GlobalTheory.JR.Hyp.pt_pt_eq_reflect F E A ψ x ν hν _ (hsw _ (hpt Φ hΦ))
    have i2 := _root_.GlobalTheory.JR.Hyp.pt_pt_eq_reflect F E A ψ x ν hν Φ hΦ
    funext p
    show pt A ν ψ x (fun q => pt A ν ψ x (pt A ν ψ x (fun q' => pt A ν ψ x Φ (q'.2, q'.1))) (q.2, q.1)) p = _
    rw [i1]
    show pt A ν ψ x (pt A ν ψ x Φ) (-p.1, p.2) = _
    rw [i2]
  have hA : ∀ f : A.L → ℂ, IsTest f → ∀ p,
      fourB μ₀ (A.kerL ψ x) f (cc A e p) = tt A ν ψ x (fun q => f (cc A e q)) p := by
    intro f hf p
    have ht : IsTest (fun z => f z * A.kerL ψ x z (cc A e p)) := ⟨hf.1.mul (hlc _), hf.2.mul_right⟩
    unfold fourB
    rw [hint _ ht]
    show _ = ∫ a, (∫ b, f (cc A e (a, b)) * kx A ψ x b p.1 ∂ν) * kx A ψ x a p.2 ∂ν
    congr 1; funext a
    rw [← integral_mul_const]
    congr 1; funext b
    rw [hker]; dsimp only; ring
  have hB : ∀ f : A.L → ℂ, IsTest f → IsTest (fourB μ₀ (A.kerL ψ x) f) := by
    intro f hf
    have : fourB μ₀ (A.kerL ψ x) f = fun y => tt A ν ψ x (fun q => f (cc A e q)) (ci A e y) := by
      funext y; have := hA f hf (ci A e y); rwa [h2] at this
    rw [this]; exact htc' _ (hT _ (htc f hf))
  have hsd : SelfDual μ₀ (A.kerL ψ x) := by
    refine ⟨inferInstance, fun f hf y => ?_⟩
    rw [← h2 y, hA _ (hB f hf)]
    have : (fun q => fourB μ₀ (A.kerL ψ x) f (cc A e q)) = tt A ν ψ x (fun q => f (cc A e q)) :=
      funext (hA f hf)
    rw [this, hTT _ (htc f hf)]
    dsimp only
    congr 1
    simp only [cc, map_neg]; ring
  have heq : μ = μ₀ := MeasScale.selfDual_unique hS (A.kerL ψ x) hsd hμ
  rw [heq]; exact hint h hh

end GlobalTheory.JR.Hyp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignedInvolutionStableLatticeSumMulFixedUnit
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.Move

variable {K : UQ} (B : InvAlg K)

theorem det_trace_ne_zero (hP : B.P.Separable)
    (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
      Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  obtain ⟨b, hb⟩ := exists_basis_pow_of_separable K B hP
  have hk : ∀ k : Fin (Module.finrank K.E B.A),
      Algebra.trace K.E B.A (B.g ^ (k : ℕ) * ∑ l, v l • e l) = 0 := by
    intro k
    have := congrFun hMv k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum, ← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hall : ∀ w : B.A, Algebra.trace K.E B.A ((∑ l, v l • e l) * w) = 0 := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr w, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_smul_comm, map_smul, hb k, mul_comm, hk k, smul_zero]
  have hz0 : ∑ l, v l • e l = 0 :=
    (Sandwich.traceForm_nondegenerate B hP).1 _ (fun w => by rw [Algebra.traceForm_apply]; exact hall w)
  apply hv
  apply e.equivFun.symm.injective
  rw [Module.Basis.equivFun_symm_apply, hz0, map_zero]

theorem mem_mulLat (M : Submodule K.O B.A) (y : B.Aˣ) (z : B.A) :
    z ∈ mulLat K.O (y : B.A) M ↔ ((y⁻¹ : B.Aˣ) : B.A) * z ∈ M := by
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, by simp⟩

theorem mulLat_inv (M : Submodule K.O B.A) (y : B.Aˣ) :
    mulLat K.O ((y⁻¹ : B.Aˣ) : B.A) (mulLat K.O (y : B.A) M) = M := by
  ext z
  rw [mem_mulLat, mem_mulLat, inv_inv, Units.inv_mul_cancel_left]

theorem mulLat_mem_Lin (y : B.Aˣ) (hy : B.σ (y : B.A) = y) (M : Submodule K.O B.A) (hM : M ∈ B.Lin) :
    mulLat K.O (y : B.A) M ∈ B.Lin := by
  obtain ⟨⟨hfg, hsp⟩, hg, hσ⟩ := hM
  have hyi : B.σ ((y⁻¹ : B.Aˣ) : B.A) = ((y⁻¹ : B.Aˣ) : B.A) := by
    have h1 : B.σ ((y⁻¹ : B.Aˣ) : B.A) * (y : B.A) = 1 := by
      conv_lhs => rw [← hy]
      rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((y⁻¹ : B.Aˣ) : B.A) = B.σ ((y⁻¹ : B.Aˣ) : B.A) * (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  refine ⟨⟨hfg.map _, ?_⟩, fun z hz => ?_, fun z hz => ?_⟩
  · have h1 : ((mulLat K.O (y : B.A) M : Submodule K.O B.A) : Set B.A) =
        (LinearMap.mulLeft K.E (y : B.A)) '' (M : Set B.A) := by
      rw [mulLat, Submodule.map_coe]
      rfl
    rw [h1, Submodule.span_image, hsp, Submodule.map_top, LinearMap.range_eq_top]
    intro x
    exact ⟨((y⁻¹ : B.Aˣ) : B.A) * x, by simp⟩
  · rw [mem_mulLat] at hz ⊢
    rw [mul_left_comm]
    exact hg _ hz
  · rw [mem_mulLat] at hz ⊢
    have := hσ _ hz
    rwa [map_mul, hyi] at this

theorem sgnLat_mulLat (hP : B.P.Separable) (M : Submodule K.O B.A) (hM : IsLat K.O K.E M)
    (hσ : ∀ y ∈ M, B.σ y ∈ M) (y : B.Aˣ) :
    B.sgnLat (mulLat K.O (y : B.A) M) = K.eta (Algebra.norm K.E (y : B.A)) * B.sgnLat M := by
  classical
  obtain ⟨e, he, -⟩ := GlobalTheory.GaloisDescentLattice.exists_fixed_basis K B M hM hσ
  let f : B.A ≃ₗ[K.E] B.A := LinearEquiv.ofLinear (LinearMap.mulLeft K.E (y : B.A))
    (LinearMap.mulLeft K.E ((y⁻¹ : B.Aˣ) : B.A)) (by ext x; simp) (by ext x; simp)
  let e' := e.map f
  have he' : ∀ l, e' l = (y : B.A) * e l := fun l => rfl
  have hspan : mulLat K.O (y : B.A) M = Submodule.span K.O (Set.range e') := by
    rw [← he, mulLat, Submodule.map_span, ← Set.range_comp]
    rfl
  have hN : Algebra.norm K.E (y : B.A) ≠ 0 := (y.isUnit.map (Algebra.norm K.E)).ne_zero
  have hmat : (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e' l)) =
      (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)) * Algebra.leftMulMatrix e (y : B.A) := by
    ext k l
    simp only [Matrix.mul_apply, Matrix.of_apply, Algebra.leftMulMatrix_eq_repr_mul]
    rw [he' l]
    conv_lhs => rw [← e.sum_repr ((y : B.A) * e l)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  rw [hspan, SgnBasis.sgnLat_span_basis, ← he, SgnBasis.sgnLat_span_basis, hmat, Matrix.det_mul,
    ← Algebra.norm_eq_matrix_det, Desc.eta_mul (det_trace_ne_zero B hP e) hN, mul_comm]

theorem inDual_mulLat (M : Submodule K.O B.A) (y : B.Aˣ) (t : B.A) :
    InDual B t (mulLat K.O (y : B.A) M) ↔ InDual B ((y : B.A) * t) M := by
  unfold InDual
  constructor
  · intro h z hz
    have := h ((y : B.A) * z) (by rw [mem_mulLat, Units.inv_mul_cancel_left]; exact hz)
    have e : t * ((y : B.A) * z) = (y : B.A) * t * z := by ring
    rwa [e] at this
  · intro h z hz
    rw [mem_mulLat] at hz
    have := h _ hz
    have e : (y : B.A) * t * (((y⁻¹ : B.Aˣ) : B.A) * z) = t * z := by
      rw [mul_comm (y : B.A) t, mul_assoc, Units.mul_inv_cancel_left]
    rwa [e] at this

theorem term_mulLat {ι : Type} (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A)
    (y : B.Aˣ) :
    term B π I I' ((y : B.A) * u) s (mulLat K.O (y : B.A) M) = term B π I I' u ((y : B.A) * s) M := by
  classical
  unfold term dlt
  congr 1
  · refine Finset.sum_congr rfl fun J _ => ?_
    unfold indM
    have e : ((y⁻¹ : B.Aˣ) : B.A) * ((∏ j ∈ J, π j) * ((y : B.A) * u)) = (∏ j ∈ J, π j) * u := by
      rw [mul_left_comm, Units.inv_mul_cancel_left]
    simp only [mem_mulLat, e]
  · refine Finset.sum_congr rfl fun J _ => ?_
    unfold indD
    have e : (y : B.A) * ((∏ j ∈ J, π j) * s) = (∏ j ∈ J, π j) * ((y : B.A) * s) := by ring
    simp only [inDual_mulLat, e]

theorem HH_mul_unit : ∀ (K : UQ) (B : InvAlg K) (ι : Type) (π : ι → B.A) (I I' : Finset ι) (u s y : B.A),
    B.LieReg → B.Plus y → HH B π I I' (y * u) s = K.eta (Algebra.norm K.E y) * HH B π I I' u (y * s) := by
  intro K B ι π I I' u s y hB hy
  obtain ⟨⟨yu, rfl⟩, hσ⟩ := hy
  have hσ' : B.σ ((yu⁻¹ : B.Aˣ) : B.A) = ((yu⁻¹ : B.Aˣ) : B.A) := by
    have h1 : B.σ ((yu⁻¹ : B.Aˣ) : B.A) * (yu : B.A) = 1 := by
      conv_lhs => rw [← hσ]
      rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((yu⁻¹ : B.Aˣ) : B.A) = B.σ ((yu⁻¹ : B.Aˣ) : B.A) * (yu : B.A) * ((yu⁻¹ : B.Aˣ) : B.A) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  unfold HH
  rw [mul_finsum_mem]
  symm
  refine finsum_mem_eq_of_bijOn (fun M => mulLat K.O (yu : B.A) M) ?_ ?_
  · refine Set.InvOn.bijOn (f' := fun M => mulLat K.O ((yu⁻¹ : B.Aˣ) : B.A) M) ⟨fun M _ => ?_, fun M _ => ?_⟩
      (fun M hM => mulLat_mem_Lin B yu hσ M hM) (fun M hM => ?_)
    · exact mulLat_inv B M yu
    · have := mulLat_inv B M yu⁻¹
      rwa [inv_inv] at this
    · have := mulLat_mem_Lin B yu⁻¹ hσ' M hM
      exact this
  · intro M hM
    rw [sgnLat_mulLat B hB.2 M hM.1 hM.2.2 yu, term_mulLat]
    ring

end GlobalTheory.UnitLemma.Move
end
end

