module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvertibleIdealPrincipalOnZariskiCover
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.ZarPrincipal

theorem form_mul_comm {A : Type} [CommRing A] (I : Ideal A) (f : Module.Dual A ↥I)
    (y x : ↥I) : f y * (x : A) = f x * (y : A) := by
  have h : (x : A) • y = (y : A) • x := by
    ext; simp [mul_comm]
  have := congrArg f h
  simp only [map_smul, smul_eq_mul] at this
  rw [mul_comm, this, mul_comm]

theorem one_mem_span_values {A : Type} [CommRing A] (I : Ideal A) [Module.Invertible A ↥I] :
    (1 : A) ∈ Ideal.span {a | ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = a} := by
  obtain ⟨t, ht⟩ := (Module.Invertible.bijective (R := A) (M := ↥I)).2 1
  rw [← ht]
  clear ht
  induction t with
  | tmul f y => exact Ideal.subset_span ⟨f, y, by simp [contractLeft_apply]⟩
  | add a b ha hb => rw [map_add (f := _)]; exact Ideal.add_mem _ ha hb

end GlobalTheory.BSP.ZarPrincipal


open GlobalTheory.BSP.ZarPrincipal in
theorem GlobalTheory.BSP.invertible_ideal_principal_on_cover :
    ∀ (A : Type) [CommRing A] (I : Ideal A), Module.Invertible A ↥I → ∃ (n : ℕ) (s t : Fin n → A),
      Ideal.span (Set.range s) = ⊤ ∧ ∀ i, t i ∈ I ∧ ∀ x ∈ I, ∃ c, s i * x = c * t i := by
  intro A _ I hI
  set S : Set A := {a | ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = a} with hS
  have h1 : (1 : A) ∈ Ideal.span S := one_mem_span_values I
  obtain ⟨T, hTS, hT⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hmem : ∀ a : T, ∃ (f : Module.Dual A ↥I) (y : ↥I), f y = (a : A) := fun a => hTS a.2
  choose f y hfy using hmem
  let e := T.equivFin
  refine ⟨T.card, fun i => ((e.symm i : T) : A), fun i => (y (e.symm i) : A), ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one]
    refine Submodule.span_mono ?_ hT
    intro a ha
    exact ⟨e ⟨a, ha⟩, by simp⟩
  · intro i
    refine ⟨(y (e.symm i)).2, fun x hx => ⟨f (e.symm i) ⟨x, hx⟩, ?_⟩⟩
    show ((e.symm i : T) : A) * x = _ * (y (e.symm i) : A)
    rw [← hfy (e.symm i)]
    exact form_mul_comm I (f (e.symm i)) (y (e.symm i)) ⟨x, hx⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysIffOfTwist
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.TwistCrys

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W] [FiniteDimensional LL W]

theorem isCrys_twist (ht : TensorCrys PD LL) (hq : QuotCrys PD LL)
    (ρ ρ' : Representation LL G V) (ν : Representation LL G W) (χ : G → LL)
    (lam : W →ₗ[LL] LL) (w : W) (hw : lam w = 1)
    (hν : ∀ g x, ν g x = χ g • x) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (cν : IsCrys PD ν) (cρ : IsCrys PD ρ) : IsCrys PD ρ' := by
  let f : V ⊗[LL] W →ₗ[LL] V := (TensorProduct.rid LL V).toLinearMap ∘ₗ lam.lTensor V
  have hf : ∀ v x, f (v ⊗ₜ x) = lam x • v := fun v x => by simp [f]
  refine hq (V ⊗[LL] W) (ρ.tprod ν) V ρ' f ?_ ?_ (ht V ρ W ν cρ cν)
  · intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul v y =>
      rw [Representation.tprod_apply, TensorProduct.map_tmul, hf, hf, hν, hρ, map_smul, map_smul,
        smul_eq_mul, mul_smul]
  · intro v
    exact ⟨v ⊗ₜ w, by rw [hf, hw, one_smul]⟩

theorem isCrys_twist_iff (ht : TensorCrys PD LL) (hq : QuotCrys PD LL) (hd : DualCrys PD LL)
    (ρ ρ' : Representation LL G V) (ν : Representation LL G W) (χ : G → LL)
    (lam : W →ₗ[LL] LL) (w : W) (hw : lam w = 1)
    (hν : ∀ g x, ν g x = χ g • x) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (cν : IsCrys PD ν) : IsCrys PD ρ ↔ IsCrys PD ρ' := by
  refine ⟨isCrys_twist PD ht hq ρ ρ' ν χ lam w hw hν hρ cν, ?_⟩
  have hinv : ∀ g, χ g⁻¹ * χ g = 1 := fun g => by
    have h1 : ν g⁻¹ (ν g w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have h2 := congrArg lam h1
    rwa [hν, hν, map_smul, map_smul, hw, smul_eq_mul, smul_eq_mul, mul_one] at h2
  refine isCrys_twist PD ht hq ρ' ρ ν.dual (fun g => χ g⁻¹) (Module.Dual.eval LL W w) lam hw
    (fun g f => ?_) (fun g x => ?_) (hd W ν cν)
  · ext x
    simp [Representation.dual_apply, Module.Dual.transpose_apply, hν]
  · rw [hρ, smul_smul, hinv, one_smul]

end Generic

theorem isCrys_iff_of_twist : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ ρ' : Representation ↥LL.1 ↥(GK K) V) (ν : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ : ↥(GK K) → ↥LL.1), (∀ g x, ν g x = χ g • x) → (∀ g x, ρ' g x = χ g • ρ g x) → IsCrys (P.PD K) ν → (IsCrys (P.PD K) ρ ↔ IsCrys (P.PD K) ρ') := by
  intro hF l _ P AI T K LL V _ _ _ _ _ ρ ρ' ν χ hν hρ cν
  have h := (fontaineFormalism_iff l P).1 (GlobalTheory.RegularRing.fontaineFormalism hF l P AI ⟨T⟩) K LL
  exact isCrys_twist_iff (P.PD K) h.2.2.2.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.2.1 ρ ρ' ν χ
    (LinearMap.proj 0) (fun _ => 1) rfl hν hρ cν

end GlobalTheory.TwistCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineOfInvariantUnitBcrisMatrix
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem isCrys_of_bcris_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsUnit U → (∀ g : ↥(GK K), (ρ g).val.map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → IsCrys (P.PD K) (qRep ρ) := by
  intro l _ K P AI T d ρ U hU hinv
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact Submodule.zero_mem _

  have hU' : IsUnit (U.map T.eB.symm) := by
    have := hU.map (T.eB.symm.mapMatrix (m := Fin d))
    simpa using this
  let Q : GL (Fin d) P.R.B := hU'.unit
  have hQ : (Q : Matrix (Fin d) (Fin d) P.R.B) = U.map T.eB.symm := hU'.unit_spec
  let b := Pi.basisFun ℚ_[l] (Fin d)
  have hmat : ∀ g : ↥(GK K), LinearMap.toMatrix b b (qRep ρ g) = (ρ g).val.map (algebraMap ℤ_[l] ℚ_[l]) := by
    intro g
    rw [LinearMap.toMatrix_eq_toMatrix']
    ext i j
    simp [qRep, LinearMap.toMatrix'_apply, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  obtain ⟨e, -, -, he⟩ := GlobalTheory.tensorBasisCoords ℚ_[l] P.R.B (Fin d → ℚ_[l]) (Fin d) b
  have key := GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix ℚ_[l] ↥(K0 K) P.R.B ↥(GK K)
    (fun g => ((P.PD K).actB g).toRingEquiv.toRingHom) (Fin d)
    (fun g => (LinearMap.toMatrix b b (qRep ρ g)).map (algebraMap ℚ_[l] P.R.B))
    (fun x => ⟨fun h => (P.PD K).invB x h, by
      rintro ⟨c, rfl⟩ g
      exact ((P.PD K).actB g).commutes c⟩) Q
    (fun g => by
      apply (T.eB.mapMatrix (m := Fin d)).injective
      rw [map_mul, hmat g, hQ]
      have hA : T.eB.mapMatrix (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])).map (algebraMap ℚ_[l] P.R.B)) =
          (ρ g).val.map (Per.zB l) := by
        ext i j
        simp only [RingEquiv.mapMatrix_apply, Matrix.map_apply]
        exact T.zB _
      have hB : T.eB.mapMatrix ((U.map T.eB.symm).map (((P.PD K).actB g).toRingEquiv.toRingHom)) =
          U.map (Per.σB (g : GQ l)) := by
        ext i j
        simp only [RingEquiv.mapMatrix_apply, Matrix.map_apply]
        change T.eB ((P.PD K).actB g (T.eB.symm (U i j))) = _
        rw [P.PD_actB, T.actB, RingEquiv.apply_symm_apply]
      have hC : T.eB.mapMatrix (U.map T.eB.symm) = U := by
        ext i j
        simp
      rw [hA, hB, hC]
      exact hinv g)
    ((Dcris (P.PD K) (qRep ρ)).map (e : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] (Fin d → P.R.B)))
    (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      have h1 : e y ∈ (Dcris (P.PD K) (qRep ρ)).map (e : (Fin d → ℚ_[l]) ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] (Fin d → P.R.B)) ↔
          y ∈ Dcris (P.PD K) (qRep ρ) := by
        constructor
        · rintro ⟨z, hz, hzy⟩
          have : z = y := e.injective hzy
          exact this ▸ hz
        · exact fun h => ⟨y, h, rfl⟩
      rw [h1]
      simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      refine forall_congr' fun g => ?_
      have h2 := he (qRep ρ g) (((((P.PD K).actB g).toAlgHom.toLinearMap).restrictScalars ℚ_[l])) y
      have h3 : actVB (P.PD K) (qRep ρ) g y = TensorProduct.map (qRep ρ g)
          ((((P.PD K).actB g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y := rfl
      rw [h3, ← e.injective.eq_iff, h2]
      rfl)
  rw [LinearEquiv.finrank_map_eq, Fintype.card_fin] at key
  rw [IsCrys, key, Module.finrank_fin_fun]

end GlobalTheory.BKLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHodgeTateIffDiagonalAdaptedBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.HTDiag

theorem theta_zero_of_pow_eq {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] (θ : R →+* S)
    {t w v : R} {n m : ℕ} (ht : t ≠ 0) (hθt : θ t = 0) (hv : θ v = 0 → v = 0)
    (h : t ^ n * w = t ^ m * v) (hnm : n ≠ m) : θ w = 0 := by
  rcases Nat.lt_or_gt_of_ne hnm with hlt | hgt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have e : t ^ (n + k + 1) = t ^ n * t ^ (k + 1) := by ring
    rw [e, mul_assoc] at h
    have hw : w = t ^ (k + 1) * v := mul_left_cancel₀ (pow_ne_zero n ht) h
    rw [hw, map_mul, map_pow, hθt, zero_pow (Nat.succ_ne_zero k), zero_mul]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    have e : t ^ (m + k + 1) = t ^ m * t ^ (k + 1) := by ring
    rw [e, mul_assoc] at h
    have hv' : v = t ^ (k + 1) * w := (mul_left_cancel₀ (pow_ne_zero m ht) h).symm
    have hv0 : v = 0 := hv (by rw [hv', map_mul, map_pow, hθt, zero_pow (Nat.succ_ne_zero k), zero_mul])
    rw [hv0, mul_zero] at h
    have h' : t ^ (k + 1) * w = 0 := (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ ht)
    have hw : w = 0 := (mul_eq_zero.1 h').resolve_left (pow_ne_zero _ ht)
    rw [hw, map_zero]

end GlobalTheory.BKLim.HTDiag


open GlobalTheory.BKLim.HTDiag in
theorem GlobalTheory.BKLim.isHT_iff_diag : ∀ (l : ℕ) [Fact l.Prime] (K K' : FinExt l) (C : Core l), C.InvdR → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (H : Hodge C ξ ρ K') (z : ℂ_[l]) (u : Matrix (Fin a) (Fin a) (ℂ_[l])), K.1 ≤ K'.1 → (u * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) ↔ IsHT C ξ ρ z u) := by
  intro l _ K K' C hI ξ hξ a ρ H z u hKK'
  constructor
  · intro hm K'' p q x y hfix hxy
    obtain ⟨hdom, hinj, hF, -⟩ := BdRField.bdR_isField l
    haveI := hdom
    set ι := algebraMap (Per.BdRp l) (Per.BdR l) with hι

    have hxiker : xi C.ε ∈ Ideal.span {ξ} := by
      rw [hξ, C.ker_theta]; exact Ideal.mem_span_singleton_self _
    obtain ⟨c0, hc0⟩ := Ideal.mem_span_singleton'.1 hxiker
    have hXu : IsUnit (ι (aDp l ξ)) := by
      have h1 := TiedUnif.isUnit_xi (core_isEps l C)
      rw [← hc0, map_mul, map_mul] at h1
      exact isUnit_of_mul_isUnit_right h1
    set e := ι (aDp l ξ) with he
    obtain ⟨i0, hie⟩ : ∃ i0, i0 * e = 1 := ⟨_, hXu.val_inv_mul⟩
    have ht0 : aDp l ξ ≠ 0 := by
      intro h0
      rw [he, h0, map_zero, mul_zero] at hie
      exact zero_ne_one (hinj (by rw [map_zero, map_one]; exact hie))

    have hVdet : IsUnit H.V.det := (Matrix.isUnit_iff_isUnit_det _).1 H.unit
    set W := H.V⁻¹ with hW
    have hVW : H.V * W = 1 := Matrix.mul_nonsing_inv _ hVdet
    have hWV : W * H.V = 1 := Matrix.nonsing_inv_mul _ hVdet
    have hWVι : W.map ι * H.V.map ι = 1 := by
      rw [← Matrix.map_mul, hWV, Matrix.map_one _ (map_zero _) (map_one _)]

    set d : Fin a → Per.BdR l := fun k => i0 ^ H.q * e ^ H.p k with hd
    set d' : Fin a → Per.BdR l := fun k => e ^ H.q * i0 ^ H.p k with hd'
    have hdd : ∀ k, d' k * d k = 1 := fun k => by
      calc d' k * d k = (i0 * e) ^ H.q * (i0 * e) ^ H.p k := by simp only [hd, hd']; ring
        _ = 1 := by rw [hie, one_pow, one_pow, one_mul]
    have hQ : H.Q = H.V.map ι * Matrix.diagonal d := by
      ext i k
      rw [Matrix.mul_diagonal, Matrix.map_apply]
      have h := H.Q_eq i k
      simp only [map_mul, map_pow] at h
      rw [← he] at h
      calc H.Q i k = (i0 * e) ^ H.q * H.Q i k := by rw [hie, one_pow, one_mul]
        _ = i0 ^ H.q * (e ^ H.q * H.Q i k) := by ring
        _ = ι (H.V i k) * d k := by rw [h]; simp only [hd]; ring
    set Qi := Matrix.diagonal d' * W.map ι with hQi
    have hQiQ : Qi * H.Q = 1 := by
      rw [hQi, hQ, Matrix.mul_assoc, ← Matrix.mul_assoc (W.map ι), hWVι, Matrix.one_mul,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext k; exact hdd k
    have hQQi : H.Q * Qi = 1 := mul_eq_one_comm.1 hQiQ
    set av := Qi *ᵥ x with hav
    have hxa : x = H.Q *ᵥ av := by rw [hav, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]

    let K3 : FinExt l := ⟨K'.1 ⊔ K''.1, by
      haveI := K'.2; haveI := K''.2; exact IntermediateField.finiteDimensional_sup _ _⟩
    have hmono : ∀ {A B : FinExt l}, A.1 ≤ B.1 → ∀ g, g ∈ GK B → g ∈ GK A := fun h g hg =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (h hx)
    have h3' : K'.1 ≤ K3.1 := le_sup_left
    have h3'' : K''.1 ≤ K3.1 := le_sup_right
    have h3 : K.1 ≤ K3.1 := hKK'.trans h3'

    have hinv : ∀ g : GQ l, g ∈ GK K3 → ∀ j, Per.σD g (av j) = av j := by
      intro g hg
      let g' : ↥(GK K) := ⟨g, hmono h3 g hg⟩
      have h1 := hfix g' (hmono h3'' g hg)
      have h2 := H.inv g' (hmono h3' g hg)
      have hσx : (fun i => Per.σD (g' : GQ l) (x i)) =
          H.Q.map (Per.σD (g' : GQ l)) *ᵥ (fun k => Per.σD (g' : GQ l) (av k)) := by
        funext i
        rw [hxa]
        exact RingHom.map_mulVec _ _ _ i
      rw [hσx, Matrix.mulVec_mulVec, h2] at h1
      have h4 : av = (fun k => Per.σD (g' : GQ l) (av k)) := by
        calc av = Qi *ᵥ x := hav
          _ = Qi *ᵥ (H.Q *ᵥ (fun k => Per.σD (g' : GQ l) (av k))) := by rw [h1]
          _ = _ := by rw [Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec]
      intro j
      exact (congrFun h4 j).symm
    choose c hcK hc using fun j => hI K3 (av j) (fun g hg => hinv g hg j)

    have hWx : ∀ k, e ^ q * (W.map ι *ᵥ x) k = e ^ p * (W.map ι *ᵥ (fun i => ι (y i))) k := by
      have hv : e ^ q • x = e ^ p • (fun i => ι (y i)) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hxy i, map_mul, map_pow]
      intro k
      have := congrFun (congrArg (fun v => W.map ι *ᵥ v) hv) k
      simpa [Matrix.mulVec_smul] using this
    have hD : ∀ k, aDp l ξ ^ (H.q + p) * (W *ᵥ y) k = aDp l ξ ^ (q + H.p k) * C.o (c k) := by
      intro k
      apply hinj
      have hck : ι (C.o (c k)) = av k := hc k
      rw [map_mul, map_mul, map_pow, map_pow, hck, RingHom.map_mulVec]
      have hak : av k = d' k * (W.map ι *ᵥ x) k := by
        rw [hav, hQi, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
      rw [hak]
      calc e ^ (H.q + p) * (W.map ι *ᵥ (fun i => ι (y i))) k = e ^ H.q * (e ^ p * (W.map ι *ᵥ (fun i => ι (y i))) k) := by ring
        _ = e ^ H.q * (e ^ q * (W.map ι *ᵥ x) k) := by rw [hWx k]
        _ = (i0 * e) ^ H.p k * (e ^ H.q * (e ^ q * (W.map ι *ᵥ x) k)) := by rw [hie, one_pow, one_mul]
        _ = e ^ (q + H.p k) * (d' k * (W.map ι *ᵥ x) k) := by simp only [hd']; ring

    have hθξ : Per.θD l (aDp l ξ) = 0 := by
      rw [(thetaD_props l).2.2.2.1 ξ]
      have : Per.θ l ξ = 0 := RingHom.mem_ker.1 (hξ ▸ Ideal.mem_span_singleton_self ξ)
      rw [this]; rfl
    have hkey : ∀ k, z ^ ((H.p k : ℤ) - H.q) * Per.θD l ((W *ᵥ y) k) =
        z ^ ((p : ℤ) - q) * Per.θD l ((W *ᵥ y) k) := by
      intro k
      by_cases hk : (H.p k : ℤ) - H.q = (p : ℤ) - q
      · rw [hk]
      · have hz : Per.θD l ((W *ᵥ y) k) = 0 := by
          refine theta_zero_of_pow_eq (Per.θD l) ht0 hθξ ?_ (hD k) ?_
          · intro h0
            rw [C.o_sec.th] at h0
            have : c k = 0 := by
              first
                | exact (algebraMap (Om l) ℂ_[l]).injective (by simpa using h0)
                | exact UniformSpace.Completion.coe_injective _ (by simpa using h0)
            rw [this, map_zero]
          · intro hn; apply hk; omega
        rw [hz, mul_zero, mul_zero]

    have hyw : y = H.V *ᵥ (W *ᵥ y) := by rw [Matrix.mulVec_mulVec, hVW, Matrix.one_mulVec]
    have hθy : (fun i => Per.θD l (y i)) = H.V.map (Per.θD l) *ᵥ (fun k => Per.θD l ((W *ᵥ y) k)) := by
      funext i
      conv_lhs => rw [hyw]
      exact RingHom.map_mulVec _ _ _ i
    have hdiag : Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) *ᵥ (fun k => Per.θD l ((W *ᵥ y) k)) =
        z ^ ((p : ℤ) - q) • (fun k => Per.θD l ((W *ᵥ y) k)) := by
      funext k
      rw [Matrix.mulVec_diagonal, hkey k]; rfl
    rw [hθy, Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hdiag, Matrix.mulVec_smul]
  · intro hHT
    ext i j
    have h := hHT K' (H.p j) H.q (fun i => H.Q i j) (fun i => H.V i j) ?_ ?_
    · have := congrFun h i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      rw [Matrix.mul_diagonal, Matrix.map_apply, Matrix.mul_apply]
      simp only [Matrix.map_apply]
      rw [this, mul_comm]
    · intro g hg
      funext i
      have := congrFun (congrFun (H.inv g hg) i) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    · intro i; exact H.Q_eq i j
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTieWeak

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem isThEmpty_of_isThOf {i : X.Tw} {ι : ℂ →+* Kbar X i} {lam : X.abelian₂ i} {I : Type} [Fintype I] {φ : I → D.host.E →+* ℂ}
    {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF D.host.E)} {χ : Formalism.L2.Host.HChar D.host.E}
    (h : IsThOf X i ι lam φ s κ 𝔣 χ) : IsThEmpty X i ι lam φ s κ 𝔣 χ := by
  classical
  obtain ⟨u, hu, hth⟩ := h
  have hQ : BlochKatoReduction.Gen.QOk X i ∅ :=
    ⟨fun _ h => absurd h (Finset.notMem_empty _), Finset.disjoint_empty_left _, fun _ h => absurd h (Finset.notMem_empty _)⟩
  obtain ⟨hfin, π, T, -, hT, hδ⟩ := hth ∅ hQ
  have he : belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))) = ∅ := Finset.image_empty _
  have hc : condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E)))) = 𝔣 := by
    rw [he]; simp [condQ]
  have := Fintype.ofFinite (PicO (condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))))))
  have t : IsToricSum φ s κ (condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))))) χ (∑ q, T q) :=
    (isToricSum_iff _ _ _ _ _ _).2 ⟨hfin, T, hT, (finsum_eq_sum_of_fintype _).symm⟩
  have key : ∀ z : ℂ, IsToricSum φ s κ (condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))))) χ z →
      IsToricSum φ s κ 𝔣 χ z := by
    rw [hc]; exact fun _ hz => hz
  refine ⟨u, ∑ q, T q, hu, key _ t, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl fun δ _ => hδ δ, ← Finset.mul_sum, ← map_sum,
    ← Finset.sum_fiberwise Finset.univ (fun q => π q⁻¹)]
  congr 2
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [show {q | π q⁻¹ = δ} = ↑(Finset.univ.filter fun q => π q⁻¹ = δ) by ext; simp, finsum_mem_coe_finset]

theorem isLamTie0_of_isLamTie : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Z : LamDat D),
    IsLamTie X Z → IsLamTie0 X Z := by
  intro D N X Z h i hi lam
  obtain ⟨-, ι, -, hι⟩ := h i hi
  obtain ⟨j, a, s, hl, ht⟩ := hι lam
  exact ⟨_, j, a, s, hl.2.1, isThEmpty_of_isThOf ht⟩

end GlobalTheory.LamTieWeak
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeOfBasisMapsToBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem semiBC_of_basis : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Type) [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] (u : M →ₛₗ[f] N) (ι : Type) (e : Module.Basis ι A M) (b : Module.Basis ι B N), (∀ i, b i = u (e i)) → SemiBC u := by
  intro A B _ _ f M _ _ N _ _ u ι e b hb Q _ _ v
  refine ⟨b.constr B (fun i => v (e i)), ?_, ?_⟩
  · intro x
    have h : (b.constr B (fun i => v (e i))).comp u = v := by
      refine e.ext fun i => ?_
      simp [LinearMap.comp_apply, ← hb, Module.Basis.constr_basis]
    exact LinearMap.congr_fun h x
  · intro w hw
    refine b.ext fun i => ?_
    rw [Module.Basis.constr_basis, hb, hw]

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBaseChangeCoefficientFieldStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residualSelmer_baseChange_coefficientField : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (k : Type) [Field k] [Algebra (X.O0 i) k] [TopologicalSpace k] [DiscreteTopology k] (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i k → Function.Surjective (algebraMap (X.O0 i) k) → IsRes i K → ∀ Q : Finset (PlE D.host), Module.Finite k (selOn bkP i ρ (1 : GE N →* kˣ) k Q) → Module.Finite K (selOn bkP i ρ (1 : GE N →* Kˣ) K Q) ∧ Module.finrank K (selOn bkP i ρ (1 : GE N →* Kˣ) K Q) = Module.finrank k (selOn bkP i ρ (1 : GE N →* kˣ) k Q) := by
  first | exact @GlobalTheory.ResSel.BaseChange.selOn_baseChange | exact GlobalTheory.ResSel.BaseChange.selOn_baseChange | (intros; apply GlobalTheory.ResSel.BaseChange.selOn_baseChange <;> assumption)
end

