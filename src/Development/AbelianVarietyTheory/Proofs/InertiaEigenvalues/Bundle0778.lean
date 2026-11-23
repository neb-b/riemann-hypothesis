module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0773
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ExistsBaseRingOfConjugationFixedTensor
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalTranslatesSpanPrescribedCoefficient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.SplitCoef.Cons

open GlobalTheory.SplitScalar

variable {D : D7}

theorem isHalf_add {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) :
    IsHalf e (u + v) := fun i j => by
  simp only [Matrix.add_apply, mul_add, hu i j, hv i j]

theorem isHalf_neg {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) : IsHalf e (-u) := fun i j => by
  simp only [Matrix.neg_apply, mul_neg, hu i j]

theorem isHalf_sub {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) :
    IsHalf e (u - v) := by
  rw [sub_eq_add_neg]; exact GlobalTheory.DownLift.SplitCoef.Cons.isHalf_add hu (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_neg hv)

theorem isHalf_nsmul {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (k : ℕ) : IsHalf e (k • u) :=
  fun i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]

theorem isHalf_zero {m n : ℕ} (e : AE D) : IsHalf e (0 : Mx D m n) := fun i j => by
  simp only [Matrix.zero_apply, mul_zero]

theorem isHalf_place_of_left {m n : ℕ} {a : AE D} (ha : a * cA D a = 0) {u : Mx D m n} (hu : IsHalf a u) :
    IsHalf (a + cA D a) u := fun i j => by
  have h : cA D a * u i j = 0 := by rw [← hu i j, ← mul_assoc, mul_comm (cA D a) a, ha, zero_mul]
  rw [add_mul, h, add_zero, hu i j]

theorem isHalf_place_of_right {m n : ℕ} {a : AE D} (ha : a * cA D a = 0) {u : Mx D m n}
    (hu : IsHalf (cA D a) u) : IsHalf (a + cA D a) u := fun i j => by
  have h : a * u i j = 0 := by rw [← hu i j, ← mul_assoc, ha, zero_mul]
  rw [add_mul, h, zero_add, hu i j]

theorem heisO_mem_locSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ)
    {h : WO S T → ℂ} (hh : h ∈ locSpan ψ S T a f) {w : WO S T} (hw : IsHalf (a + cA D a) w) :
    heisO ψ S T w h ∈ locSpan ψ S T a f := by
  induction hh using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u, hu, rfl⟩ := hp
    rw [heisO_heisO]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w + u, GlobalTheory.DownLift.SplitCoef.Cons.isHalf_add hw hu, rfl⟩)
  | zero =>
    rw [show heisO ψ S T w 0 = 0 from (heisL ψ S T w).map_zero]
    exact Submodule.zero_mem _
  | add p q _ _ hp hq =>
    rw [show heisO ψ S T w (p + q) = heisO ψ S T w p + heisO ψ S T w q from (heisL ψ S T w).map_add p q]
    exact Submodule.add_mem _ hp hq
  | smul c p _ hp =>
    rw [heisO_smul]
    exact Submodule.smul_mem _ _ hp

theorem self_mem_locSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ) :
    f ∈ locSpan ψ S T a f :=
  Submodule.subset_span ⟨0, GlobalTheory.DownLift.SplitCoef.Cons.isHalf_zero _, (heisO_zero ψ S T f).symm⟩

end GlobalTheory.DownLift.SplitCoef.Cons


open GlobalTheory.SplitScalar GlobalTheory.DownLift.SplitCoef.Cons in
theorem GlobalTheory.DownLift.SplitCoef.exists_locSpan_coef_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ Φ : WO S T → ℂ, IsSBHalf a (latH S T ΛS ΛT) Φ → ∀ x₁, IsHalf a x₁ → ∃ f' ∈ locSpan ψ S T a f, ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f') = Φ x * ℓ (heisO ψ S T x₁ f) := by
  intro D ψ S T hψ ΛS ΛT hS hT a ha f hf Φ hΦ x₁ hx₁
  classical
  obtain ⟨⟨k₀, hk₀, hinv, hsupp⟩, -, -⟩ := GlobalTheory.DownLift.SplitCoef.coef_isSBHalf_uniform D ψ S T hψ ΛS ΛT hS hT a ha f hf
  obtain ⟨hΦs, kΦ, hkΦ, hΦinv, hΦsupp⟩ := hΦ
  obtain ⟨k₁, hk₁, hx₁Λ⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_latO
    (GlobalTheory.PlaceVec.selfDual_isFullLattice S ΛS hS)
    (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hT) x₁ (half_fin ha hx₁)
  obtain ⟨k, hk, hfix, hΦk, hkx₁, hk0, hkΦ'⟩ : ∃ k : ℕ, 0 < k ∧
      (∀ u ∈ latH S T ΛS ΛT, IsHalf a u → heisO ψ S T (k • u) f = f) ∧
      (∀ u ∈ latH S T ΛS ΛT, IsHalf a u → ∀ t, Φ (t + k • u) = Φ t) ∧
      k • x₁ ∈ latH S T ΛS ΛT ∧
      (∀ y, k₀ • y ∈ latH S T ΛS ΛT → k • y ∈ latH S T ΛS ΛT) ∧
      (∀ y, kΦ • y ∈ latH S T ΛS ΛT → k • y ∈ latH S T ΛS ΛT) := by
    refine ⟨k₀ * kΦ * k₁, by positivity, fun u hu hua => ?_, fun u hu hua t => ?_, ?_, fun y hy => ?_,
      fun y hy => ?_⟩
    · rw [mul_assoc, mul_smul]
      exact hinv _ (AddSubgroup.nsmul_mem _ hu _) (Or.inl (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua _))
    · rw [show k₀ * kΦ * k₁ = kΦ * (k₀ * k₁) by ring, mul_smul]
      exact hΦinv _ (AddSubgroup.nsmul_mem _ hu _) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua _) t
    · rw [mul_smul]
      exact AddSubgroup.nsmul_mem _ hx₁Λ _
    · rw [show k₀ * kΦ * k₁ = (kΦ * k₁) * k₀ by ring, mul_smul]
      exact AddSubgroup.nsmul_mem _ hy _
    · rw [show k₀ * kΦ * k₁ = (k₀ * k₁) * kΦ by ring, mul_smul]
      exact AddSubgroup.nsmul_mem _ hy _
  have hca : IsSplitIdem D (cA D a) := isSplitIdem_conj ha
  have hcaa : cA D a * a = 0 := by rw [mul_comm]; exact ha.2.1
  obtain ⟨Y, hYne, hY, -, hYsum⟩ :=
    GlobalTheory.DownLift.GenQuot.reps_orth D ψ S T hψ ΛS ΛT hS hT a ha.1 (infPart_splitIdem ha) k hk
  obtain ⟨X, -, hX, hXu, -⟩ :=
    GlobalTheory.DownLift.GenQuot.reps_orth D ψ S T hψ ΛS ΛT hS hT (cA D a) hca.1 (infPart_splitIdem hca) k hk
  simp only [GlobalTheory.DualPairCheck.cA_cA] at hX hXu
  obtain ⟨n, hn⟩ : ∃ n, n = ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x₁ f) := ⟨_, rfl⟩

  have hA : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x n) =
      if (∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) then (Y.card : ℂ) * ℓ (heisO ψ S T x₁ f) else 0 := by
    intro ℓ hℓ x hx
    have hg : IsThetaFunO ψ S T (heisO ψ S T x₁ f) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf x₁
    have hxg : IsThetaFunO ψ S T (heisO ψ S T x (heisO ψ S T x₁ f)) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg x
    have h1 : ℓ (heisO ψ S T x n) =
        (∑ y ∈ Y, ψ (symplO S T x y)) * ℓ (heisO ψ S T x (heisO ψ S T x₁ f)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hn, heisO_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [heisO_comm, ℓ.map_smul, smul_eq_mul, hℓ y (hY y hy).1 _ hxg]
    have h2 : heisO ψ S T x (heisO ψ S T x₁ f) = heisO ψ S T (x + x₁) f :=
      (heisO_add_of_orth ψ S T (symplO_eq_zero S T hcaa hx hx₁) f).symm
    rw [h1, h2]
    split_ifs with hP
    · obtain ⟨u, hu, hua, rfl⟩ := hP
      have hkx : k • (k • u) ∈ latH S T ΛS ΛT := AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hu _) _
      rw [Finset.sum_congr rfl fun y hy => (hYsum (k • u) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua k) hkx).1 ⟨u, hu, hua, rfl⟩ y hy,
        Finset.sum_const, nsmul_eq_mul, mul_one]
      have horth : symplO S T x₁ (k • u) = 0 := symplO_eq_zero S T hcaa hx₁ (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua k)
      rw [add_comm, heisO_add_of_orth ψ S T horth f, hfix u hu hua]
    · by_cases hkx : k • x ∈ latH S T ΛS ΛT
      · rw [(hYsum x hx hkx).2 hP, zero_mul]
      · have h3 : ℓ (heisO ψ S T (x + x₁) f) = 0 := by
          by_contra hne
          apply hkx
          have h4 := hk0 _ (hsupp ℓ hℓ (x + x₁) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_add hx hx₁) hne)
          have h5 : k • x = k • (x + x₁) - k • x₁ := by rw [nsmul_add, add_sub_cancel_right]
          rw [h5]
          exact AddSubgroup.sub_mem _ h4 hkx₁
        rw [h3, mul_zero]
  refine ⟨((Y.card : ℂ)⁻¹) • ∑ z ∈ X, Φ z • heisO ψ S T (-z) n, ?_, ?_⟩
  · have hg : heisO ψ S T x₁ f ∈ locSpan ψ S T a f :=
      heisO_mem_locSpan ψ S T a f (self_mem_locSpan ψ S T a f) (isHalf_place_of_left ha.2.1 hx₁)
    have hnm : n ∈ locSpan ψ S T a f := by
      rw [hn]
      exact Submodule.sum_mem _ fun y hy =>
        heisO_mem_locSpan ψ S T a f hg (isHalf_place_of_right ha.2.1 (hY y hy).1)
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _
      (heisO_mem_locSpan ψ S T a f hnm (isHalf_place_of_left ha.2.1 (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_neg (hX z hz).1))))
  · intro ℓ hℓ x hx
    have hc : (Y.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hYne.card_pos.ne'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [heisO_smul, heisO_sum, ℓ.map_smul, map_sum, smul_eq_mul]
    have hterm : ∀ z ∈ X, ℓ (heisO ψ S T x (Φ z • heisO ψ S T (-z) n)) = Φ x *
        (if (∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x - z = k • u) then (Y.card : ℂ) * ℓ (heisO ψ S T x₁ f)
          else 0) := by
      intro z hz
      have hzh := (hX z hz).1
      rw [heisO_smul, ℓ.map_smul, smul_eq_mul,
        ← heisO_add_of_orth ψ S T (symplO_eq_zero S T hcaa hx (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_neg hzh)) n, ← sub_eq_add_neg,
        hA ℓ hℓ (x - z) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_sub hx hzh)]
      split_ifs with hP
      · obtain ⟨u, hu, hua, hxu⟩ := hP
        rw [(sub_eq_iff_eq_add').1 hxu, hΦk u hu hua]
      · rw [mul_zero, mul_zero]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    by_cases hΦx : Φ x = 0
    · rw [hΦx, zero_mul, mul_zero, zero_mul]
    · obtain ⟨z₀, ⟨hz₀, hP₀⟩, huniq⟩ := hXu x hx (hkΦ' x (hΦsupp x hΦx))
      rw [Finset.sum_eq_single_of_mem z₀ hz₀ (fun z hz hne => if_neg fun hP => hne (huniq z ⟨hz, hP⟩)),
        if_pos hP₀]
      field_simp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrincipalRoot
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistLeft

theorem exists_principal_root {D : D7} (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    ∃ e : D.host.Eˣ, IsDetRoot V γ (Units.map (incA D).toMonoidHom e) := by
  obtain ⟨γ₀, -, h0⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  have hdet : ((matHom V γ).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det =
      incA D γ₀.1.det := by
    rw [← GlobalTheory.DetRootRows.det_bc, h0]; rfl
  generalize γ₀.1.det = d at hdet
  have hc : ∀ e : D.host.E, cA D (incA D e) = incA D (star e) := fun e => rfl
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  have hn : star d * d = 1 := by
    have := det_conj_mul V γ
    apply GlobalTheory.DetRootRows.inclR_injective (F := D.host.F) (AF D.host.F)
    rw [map_mul, map_one, ← hc, ← hdet]
    exact this
  obtain ⟨e, he0, he⟩ : ∃ e : D.host.E, e ≠ 0 ∧ e = d * star e := by
    by_cases hd : d = -1
    · obtain ⟨a, ha⟩ := GlobalTheory.RecDict.cmData_sig_ne_id D.sp.cm
      refine ⟨a - star a, sub_ne_zero.2 (Ne.symm ha), ?_⟩
      rw [hd, star_sub, star_star]; ring
    · refine ⟨1 + d, fun h => hd (by linear_combination h), ?_⟩
      rw [star_add, star_one]; linear_combination -hn
  refine ⟨Units.mk0 e he0, ?_⟩
  unfold IsDetRoot
  rw [hdet]
  show incA D e = incA D d * cA D (incA D e)
  rw [hc, ← map_mul, ← he]

theorem muVal_left {D : D7} (V : HSp D) (χ : (AE D)ˣ →* Circle)
    (hE : ∀ x : D.host.Eˣ, χ (Units.map (incA D).toMonoidHom x) = 1) (mu : GA D V → ℂ) (hmu : MuVal V χ mu)
    (γ : GA D V) (hγ : γ ∈ GQ V) (h : GA D V) : mu (γ * h) = mu h := by
  obtain ⟨x, hx⟩ := hmu.1 h
  obtain ⟨e, he⟩ := exists_principal_root V γ hγ
  rw [hmu.2 _ _ (detRootMul_holds V γ h _ x he hx), hmu.2 h x hx, map_mul, hE e, one_mul]

theorem twist_left : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E)
    (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) →
    ∀ γ ∈ GQ V, ∀ h : GA D V, dd (γ * h) = dd h := by
  intro D V pd k _ σ δ δc ht dd hdd γ hγ h
  have hE : ∀ x : D.host.Eˣ, δc (Units.map (incA D).toMonoidHom x) = 1 := ht.1.1.2
  rcases hdd with hm | hm
  · exact muVal_left V δc hE dd hm γ hγ h
  · exact muVal_left V δc⁻¹ (fun x => by rw [MonoidHom.inv_apply, hE x, inv_one]) dd hm γ hγ h

end GlobalTheory.TwistLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FamilyUniformisationPointsEqMarkedIsometry
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix

noncomputable section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.PermUnif

variable {g g' : ℕ}

def permCLE (π : Fin g ≃ Fin g') : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ π).toContinuousLinearEquiv

@[simp] theorem permCLE_apply (π : Fin g ≃ Fin g') (z : Fin g' → ℂ) (j : Fin g) : permCLE π z j = z (π j) := rfl

@[simp] theorem permCLE_symm_apply (π : Fin g ≃ Fin g') (z : Fin g → ℂ) (j : Fin g') :
    (permCLE π).symm z j = z (π.symm j) := by
  have : permCLE π (fun j' => z (π.symm j')) = z := funext fun j => by simp
  rw [(permCLE π).symm_apply_eq.2 this.symm]

def permP {L : Type} [AddCommGroup L] (π : Fin g ≃ Fin g') (P : L →+ (Fin g → ℂ)) : L →+ (Fin g' → ℂ) where
  toFun a j := P a (π.symm j)
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp] theorem permP_apply {L : Type} [AddCommGroup L] (π : Fin g ≃ Fin g') (P : L →+ (Fin g → ℂ)) (a : L)
    (j : Fin g') : permP π P a j = P a (π.symm j) := rfl

theorem permCLE_permP {L : Type} [AddCommGroup L] (π : Fin g ≃ Fin g') (P : L →+ (Fin g → ℂ)) (a : L) :
    permCLE π (permP π P a) = P a := funext fun j => by simp

theorem hermForm_perm (π : Fin g ≃ Fin g') (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g' → ℂ) :
    hermForm (Hm.submatrix π.symm π.symm) z w = hermForm Hm (permCLE π z) (permCLE π w) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Pi.star_apply, permCLE_apply]
  rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp π]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem isPeriod_permP {D : Datum H} {ty : Fin g → (E →+* ℂ)} {ty' : Fin g' → (E →+* ℂ)} (π : Fin g ≃ Fin g')
    (hπ : ∀ j, ty' (π j) = ty j) {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) : IsPeriod D ty' (permP π P) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, hEF⟩ := hP
  refine ⟨fun a x j => ?_, fun x y hxy => hinj (funext fun j => ?_), ?_, ?_,
    ⟨Hm.submatrix π.symm π.symm, hH.submatrix _, fun z hz => ?_, fun x y => ?_⟩⟩
  · rw [permP_apply, permP_apply, hlin, ← hπ, Equiv.apply_symm_apply]
  · have := congrFun hxy (π j)
    simpa using this
  · haveI := hdisc
    refine DiscreteTopology.of_continuous_injective (f := fun v : (permP π P).range =>
      (⟨permCLE π v.1, ?_⟩ : P.range)) ?_ ?_
    · obtain ⟨x, hx⟩ := v.2
      exact ⟨x, by rw [← hx, permCLE_permP]⟩
    · exact Continuous.subtype_mk ((permCLE π).continuous.comp continuous_subtype_val) _
    · intro v w hvw
      exact Subtype.ext ((permCLE π).injective (congrArg Subtype.val hvw))
  · have hr : Set.range (permP π P) = ((permCLE π).symm.toLinearEquiv.restrictScalars ℝ).toLinearMap '' Set.range P := by
      ext v
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨P x, ⟨x, rfl⟩, ?_⟩
        funext j
        simp
      · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, funext fun j => by simp⟩
    rw [hr, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact ((permCLE π).symm.toLinearEquiv.restrictScalars ℝ).surjective
  · rw [hermForm_perm]
    refine hpos _ fun h0 => hz (funext fun j => ?_)
    have := congrFun h0 (π.symm j)
    simpa using this
  · rw [hermForm_perm, permCLE_permP, permCLE_permP, hEF]

theorem isHolTo_comp_cle {X : Scheme.{0}} (L : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ)) {y : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (hy : IsHolTo Set.univ y) : IsHolTo Set.univ (fun z => y (L z)) := by
  intro U f
  obtain ⟨ho, hd⟩ := hy U f
  have hs : {b ∈ (Set.univ : Set (Fin g' → ℂ)) | ⊤ ≤ y (L b) ⁻¹ᵁ U} = L ⁻¹' {b ∈ Set.univ | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    simp
  rw [hs]
  exact ⟨ho.preimage L.continuous, hd.comp L.differentiableOn (fun b hb => hb)⟩

theorem isDerivAt0_comp_cle {X : Scheme.{0}} (L : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ)) (y : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (w : Fin g' → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 (fun z => y (L z)) w v ↔ IsDerivAt0 y (L w) v := by
  unfold IsDerivAt0
  simp only [map_zero]
  refine and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun h => forall_congr' fun f => ?_)
  rw [show (fun z => valAt' (y (L z)) U f) = (fun z => valAt' (y z) U f) ∘ L from rfl, L.comp_right_fderiv,
    map_zero]
  rfl

theorem isometry_of_point_eq_perm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g g' : ℕ}
    {ty : Fin g → (E →+* ℂ)} {ty' : Fin g' → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (F' : FamilyUnif Xo σ' ty')
    (hpq : 1 ≤ Dw.p + Dw.q) (hσ : σ' (baseKA l).ρ = H.rt0) (hty : IsTypeFn H Dw.p Dw.q ty)
    (hty' : IsTypeFn H Dw.p Dw.q ty') (π : Fin g ≃ Fin g') (hπ : ∀ j, ty' (π j) = ty j)
    (k : Fin F.n) (k' : Fin F'.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (P' : (F'.Di k').La →+ (Fin g' → ℂ))
    (hP : IsPeriod (F.Di k) ty P) (hP' : IsPeriod (F'.Di k') ty' P') (h : F.u k P = F'.u k' P'), ∃ gam : (F.Di k).La ≃ₗ[𝓞 E] (F'.Di k').La, (∀ a b, (F'.Di k').EF (gam a) (gam b) = (F.Di k).EF a b) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t k a) = F'.t k' a + l.M • x := by
  intro E _ _ _ H Dw l Xo σ' g g' ty ty' F F' hpq hσ hty hty' π hπ k k' P P' hP hP' h
  have hL : ∀ a, permCLE π (permP π P a) = P a := permCLE_permP π P
  have hd := F.ex_diff k P hP
  have key := GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all
    GlobalTheory.firstFiveLaws.1 E H Dw l Xo σ' g' ty' hpq hσ hty' (F.Di k) (F'.Di k') (F.t k) (F'.t k') (permP π P) P'
    (F.u k P) (F'.u k' P') (fun z => F.ex k P (permCLE π z)) (F'.ex k' P')
  obtain ⟨gam, -, hEF, hM, -, -⟩ := (key (by
    refine ⟨F.over_σ k P hP, isPeriod_permP π hπ hP, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro z w
      rw [map_add (f := _)]
      exact F.ex_add k P hP _ _
    · exact (F.ex_onto k P hP).comp (permCLE π).surjective
    · exact isHolTo_comp_cle (permCLE π) (y := fun z => (F.ex k P z).left) (GlobalTheory.ClassUniq.isHolTo_ex F k P hP)
    · intro w
      obtain ⟨v, hv, hu⟩ := hd.1 (permCLE π w)
      exact ⟨v, (isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) w v.left).2 hv,
        fun v' hv' => hu v' ((isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) w v'.left).1 hv')⟩
    · intro v hv
      have h0 : (permCLE π) 0 = 0 := map_zero _
      have hv0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (F.ex k P 0).left := by
        rw [← h0]; exact hv
      obtain ⟨w, hw, hu⟩ := hd.2 v hv0
      refine ⟨(permCLE π).symm w, (isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) _ v.left).2 (by
        rwa [(permCLE π).apply_symm_apply]), fun w' hw' => ?_⟩
      rw [← hu _ ((isDerivAt0_comp_cle (permCLE π) (fun z => (F.ex k P z).left) w' v.left).1 hw'),
        (permCLE π).symm_apply_apply]
    · intro z
      refine (F.ex_ker k P hP (permCLE π z)).trans ⟨?_, ?_⟩
      · rintro ⟨x, hx⟩
        refine ⟨x, funext fun j => ?_⟩
        have := congrFun hx (π.symm j)
        simpa using this
      · rintro ⟨x, rfl⟩
        exact ⟨x, (hL x).symm⟩
    · intro a z
      have e : permCLE π (fun j => ty' j (a : E) * z j) = fun j => ty j (a : E) * permCLE π z j :=
        funext fun j => by simp [hπ]
      rw [e]
      exact F.ex_lin k P hP a (permCLE π z)
    · intro n a a₂ c hn hc
      rw [map_smul, map_smul, hL, hL]
      exact F.ex_weil k P hP n a a₂ c hn hc
    · intro a ha
      rw [map_smul, hL]
      exact F.ex_eta k P hP a ha
    · intro a
      rw [map_smul, hL]
      exact F.ex_etaA k P hP a) (by
    exact ⟨F'.over_σ k' P' hP', hP', ⟨F'.ex_add k' P' hP', F'.ex_onto k' P' hP', GlobalTheory.ClassUniq.isHolTo_ex F' k' P' hP',
      (F'.ex_diff k' P' hP').1, (F'.ex_diff k' P' hP').2⟩, F'.ex_ker k' P' hP', F'.ex_lin k' P' hP',
      F'.ex_weil k' P' hP', F'.ex_eta k' P' hP', F'.ex_etaA k' P' hP'⟩)).1 h
  exact ⟨gam, hEF, hM⟩

end GlobalTheory.PermUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOFixOfIsThetaAt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.VacFix

variable {D : D7}

theorem symplO_eq_zero (S T : HSp D) (x y : WO S T)
    (h : ∀ c b d a, cA D (y c b) * x d a = 0) : symplO S T x y = 0 := by
  have h0 : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    have := h c b d a
    calc _ = incA D ((HSpace.gram S)⁻¹ a b) * incA D (HSpace.gram T c d) *
        (cA D (y c b) * x d a) := by ring
      _ = 0 := by rw [this, mul_zero]
  unfold symplO
  rw [h0, mul_zero, map_zero]

theorem heisO_fix_of_isThetaAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (c : ℂ) (f₀ Φ f : WO S T → ℂ) (u : WO S T), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → (∀ i j, e * u i j = 0) → (∀ i j, cA D e * u i j = 0) → heisO ψ S T u f₀ = f₀ → heisO ψ S T u f = f := by
  intro D ψ S T e Λ c f₀ Φ f u hf h1 h2 h0
  obtain ⟨⟨M, hM⟩, hall⟩ := hf
  have hM' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀
      ((GlobalTheory.SplitScalar.heisL ψ S T u) ∘ₗ M) := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
      rw [hM.trans Ψ hΨ x hx, GlobalTheory.SplitScalar.heisO_comm, symplO_eq_zero, AddChar.map_zero_eq_one,
        one_smul]
      intro c b d a
      rw [← hx c b, map_mul]
      linear_combination cA D (x c b) * h2 d a
    · simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
      rw [hM.modul Ψ hΨ y hy, GlobalTheory.SplitScalar.heisO_comm ψ S T y u, symplO_eq_zero,
        AddChar.map_zero_eq_one, one_smul]
      intro c b d a
      have h3 : cA D e * cA D (u c b) = 0 := by rw [← map_mul, h1, map_zero]
      rw [← hy d a]
      linear_combination y d a * h3
    · simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
      rw [hM.vac, h0]
  have e1 := hall M hM
  have e2 := hall _ hM'
  simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply] at e2
  rw [← e1] at e2
  exact e2.symm

end GlobalTheory.VacFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentRepresentation
section
namespace GlobalTheory

theorem segmentRepresentation' : GlobalTheory.Published.SegmentRepresentation :=
  CompanionTheory.RgGu.segmentRepresentation

end GlobalTheory
end

