module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralUnitGLEqHermitianLatticeCoStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_unitGL_eq_hermitianLatticeCount : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (β : B.Aˣ) (ε : B.A), (ε = 1 ∨ ε = -1) → B.σ (β : B.A) = β * (ε * B.g) → ∀ (b : Module.Basis (Fin a) K.E B.A) (δ : GLw a w), (∀ i j, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm β (b i) (b j))) → twOrb (thL a w) (GlobalTheory.LFun.KGL w (n := a)) δ ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = ((GlobalTheory.UnitLemma.orbSum K.O B.T {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm β y z ∈ (algebraMap K.O K.E).range} (fun _ => 1) : ℚ) : ℂ) := by
  first | exact @GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum | exact GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum | (intros; apply GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingSectionsFiniteType
section
set_option autoImplicit false

namespace GlobalTheory.DegCmp

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree
open GlobalTheory.FlagTan GlobalTheory.FlatLine
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem fChart_exists_val {h : GenFrEx Xo c} (C : Reg.FChart h) {e : Formalism.L2.Pj.Ix Dw → ℤ} {f : Rul Xo c}
    (hf : f ∈ secZ Xo c e) : ∃ b : C.R, (b : Om C.Z) = ((∏ i, C.t i ^ e i : (Om C.Z)ˣ) : Om C.Z) * genVal C.Z f ∧
      ∀ (S : Type) [CommRing S] [Algebra c.F S] (ψ : C.R →ₐ[c.F] S) (z : FrPt Xo c S), FrMap ψ C.y z →
        evR Xo c f z = ψ b := by
  have hL : Reg.EvLaws Xo c := (Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  obtain ⟨q, χ, y₀, hy₀⟩ := hL.test C.R C.y
  refine ⟨χ (f q y₀), ?_, fun S _ _ ψ z hz => ?_⟩
  · rw [genVal_apply h, evC, ← evR_frBor hf C.bor,
      evR_eq hf.1 (frMap_comp (χ := C.R.val.comp χ) hy₀ C.gen fun _ => rfl)]
    rfl
  · rw [evR_eq hf.1 (frMap_comp (χ := ψ.comp χ) hy₀ hz fun _ => rfl), AlgHom.comp_apply]

theorem genVal_idem_self (Z : Comp Xo c) : genVal Z (idem Z) = 1 := by
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  rw [genVal_apply h, evC]
  exact evR_idem (liesOn_genFr h Z) (fromTest_of_isLocalRing _)

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem fChart_evR_idem {h : GenFrEx Xo c} (C : Reg.FChart h) {S : Type} [CommRing S] [Algebra c.F S]
    {ψ : C.R →ₐ[c.F] S} {z : FrPt Xo c S} (hz : FrMap ψ C.y z) : evR Xo c (idem C.Z) z = 1 := by
  obtain ⟨b, hb, hb'⟩ := fChart_exists_val C (idem_mem_secZ C.Z)
  have : b = 1 := Subtype.ext (by simpa [genVal_idem_self] using hb)
  rw [hb' S ψ z hz, this, map_one]

theorem exists_fChart (h : GenFrEx Xo c) (Z : Comp Xo c) : ∃ C : Reg.FChart h, C.Z = Z := by
  obtain ⟨C, ψ, z, t', hz, hb⟩ := (Reg.evLaws_genFr_atlas E H Dw l Xo c).2.2.2 h (Om Z) (genFr h Z)
  refine ⟨C, by_contra fun hne => ?_⟩
  have h1 : evR Xo c (idem C.Z) (genFr h Z) = 0 := evC_eq_zero h (Ne.symm hne) (idem_mem_suppOn C.Z)
  rw [evR_frBor (idem_mem_secZ C.Z) hb, fChart_evR_idem C hz] at h1
  simp at h1

attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem exists_chart_read_at_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Unf Xo c σ r), IsUnf U → ∀ Z : Comp Xo c, ∃ (R : Subalgebra c.F (Om Z)) (_ : Algebra.FiniteType c.F R) (t : Formalism.L2.Pj.Ix Dw → (Om Z)ˣ), (∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, ((∏ i, t i ^ e i : (Om Z)ˣ) : Om Z) * genVal Z f ∈ R) ∧ ∀ φ : R →+* ℂ, φ.comp (algebraMap c.F R) = σ → ∃ z ∈ framesOn U Z, ∃ s : Formalism.L2.Pj.Ix Dw → ℂˣ, ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, ∀ b : R, (b : Om Z) = ((∏ i, t i ^ e i : (Om Z)ˣ) : Om Z) * genVal Z f → φ b = ((∏ i, s i ^ e i : ℂˣ) : ℂ) * rdU U f z.1 z.2 := by
  intro E _ _ _ H Dw l Xo c r σ U hU Z
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  obtain ⟨C, rfl⟩ := exists_fChart h Z
  haveI := C.sm
  refine ⟨C.R, inferInstance, C.t, fun e f hf => ?_, fun φ hφ => ?_⟩
  · obtain ⟨b, hb, -⟩ := fChart_exists_val C hf
    exact hb ▸ b.2
  · haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
    let ψ : C.R →ₐ[c.F] CAt σ := { (φ : C.R →+* CAt σ) with commutes' := fun a => DFunLike.congr_fun hφ a }
    obtain ⟨z, hz⟩ := exists_frMap ψ C.y
    obtain ⟨k, x, s, hs⟩ := hU.2.2.1 z
    have key : ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e,
        toC (σ := σ) (evR Xo c f z) = ((∏ i, (show ℂˣ from s i) ^ e i : ℂˣ) : ℂ) * rdU U f k x.1 := fun e f hf => by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, x.2, dif_pos]
      exact evR_frBor (S := CAt σ) hf hs
    refine ⟨⟨k, x.1⟩, by_contra fun hn => ?_, s, fun e f hf b hb => ?_⟩
    · have h1 := key 0 _ (idem_mem_secZ C.Z)
      rw [rdU_eq_zero U (idem_mem_suppOn C.Z) hn, mul_zero, fChart_evR_idem C hz] at h1
      exact one_ne_zero (α := ℂ) h1
    · obtain ⟨b', hb', h2⟩ := fChart_exists_val C hf
      obtain rfl : b = b' := Subtype.ext (hb.trans hb'.symm)
      exact (h2 _ ψ z hz).symm.trans (key e f hf)

end GlobalTheory.DegCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedNonzeroStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_closed_nonzero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), H'.x ≠ 0 → IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  first | exact @GlobalTheory.UnipClosed.isClosed_unip | exact GlobalTheory.UnipClosed.isClosed_unip | (intros; apply GlobalTheory.UnipClosed.isClosed_unip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorCommuteWeightVectorFunctionE
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.BCT.TrKer

theorem finsum_comp_eq_comp_finsum {ι V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : V →ₗ[ℂ] W) (g : ι → W →ₗ[ℂ] W) (h : ι → V →ₗ[ℂ] V) (hc : ∀ i, g i ∘ₗ T = T ∘ₗ h i)
    (hs : ∀ i, g i = 0 ↔ h i = 0) : (∑ᶠ i, g i) ∘ₗ T = T ∘ₗ ∑ᶠ i, h i := by
  have hg : Function.support g = Function.support h := by
    ext i; simp only [Function.mem_support, ne_eq, hs]
  by_cases hfin : (Function.support h).Finite
  · rw [finsum_eq_sum_of_support_subset g (s := hfin.toFinset) (by rw [hg]; simp),
      finsum_eq_sum_of_support_subset h (s := hfin.toFinset) (by simp)]
    ext x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun (hc i) x
  · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support (by rwa [hg])]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem RF_apply' (x : finU (E := E) (n := n)) (φ : UA E n → ℂ) (g : UA E n) : RF E n x φ g = φ (g * x.1) := rfl

theorem RF_ne_zero (x : finU (E := E) (n := n)) : RF E n x ≠ 0 := by
  intro h
  have := congrFun (LinearMap.congr_fun h (fun _ => (1 : ℂ))) 1
  simp at this
  exact one_ne_zero this

theorem rightReg_dual_ne_zero (lam : InfinitePlace E → DomWeight n) [Nontrivial (Wsp lam)] (x : finU (E := E) (n := n)) :
    rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) x ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : Wsp lam)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (Wsp lam), φ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 hc)
  intro h
  have := congrFun (LinearMap.congr_fun h (fun _ => φ)) 1
  have h2 : φ = 0 := by simpa [rightReg, LinearMap.funLeft] using this
  exact hφ (by rw [h2]; rfl)

theorem hop_phiFun (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (w : Wsp lam) :
    hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w := by
  rcases subsingleton_or_nontrivial (Wsp lam) with hW | hW
  · rw [Subsingleton.elim w 0]; simp
  set T : (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (UA E n → ℂ) := (phiFun lam).flip w with hT
  have key : (∑ᶠ q : finU (E := E) (n := n) ⧸ globLev S K', globFn S f q.out • (RF E n q.out ∘ₗ LinearMap.id)) ∘ₗ T =
      T ∘ₗ ∑ᶠ q : finU (E := E) (n := n) ⧸ globLev S K', globFn S f q.out •
        (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id) := by
    refine finsum_comp_eq_comp_finsum T _ _ (fun q => ?_) (fun q => ?_)
    · ext G g
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, hT, LinearMap.flip_apply,
        LinearMap.map_smul, Pi.smul_apply]
      rw [RF_apply', phiFun_mul_fin]
    · rw [smul_eq_zero, smul_eq_zero, LinearMap.comp_id, LinearMap.comp_id]
      simp only [RF_ne_zero, rightReg_dual_ne_zero, or_false]
  have := LinearMap.congr_fun key F
  simp only [LinearMap.comp_apply, hT, LinearMap.flip_apply] at this
  simp only [hop, hopM, levOp, LinearMap.smul_apply, this, LinearMap.map_smul]

theorem hop_phiFun_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (w : Wsp lam), hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w :=
  fun _ _ _ _ _ S lam K' f F w => hop_phiFun S lam K' f F w

end GlobalTheory.BCT.TrKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorVectorMemLevelFunctions
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.BCT.TrKer.HopStab

theorem toSub_mul_right {G : Type} [Group G] (H : Subgroup G) (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) (y : G) (k : H) (hk : k ∈ K) :
    u (toSub H (y * k)) = u (toSub H y) := by
  unfold toSub
  by_cases hy : y ∈ H
  · have h2 : y * (k : G) ∈ H := H.mul_mem hy k.2
    rw [dite_eq_left h2, dite_eq_left hy]
    exact hu k hk ⟨y, hy⟩
  · have h2 : y * (k : G) ∉ H := fun h => hy (by simpa using H.mul_mem h (H.inv_mem k.2))
    rw [dite_eq_right h2, dite_eq_right hy]

theorem toSub_mul_left {G : Type} [Group G] (H : Subgroup G) (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (k * x) = u x) (y : G) (k : H) (hk : k ∈ K) :
    u (toSub H (k * y)) = u (toSub H y) := by
  unfold toSub
  by_cases hy : y ∈ H
  · have h2 : (k : G) * y ∈ H := H.mul_mem k.2 hy
    rw [dite_eq_left h2, dite_eq_left hy]
    exact hu k hk ⟨y, hy⟩
  · have h2 : (k : G) * y ∉ H := fun h => hy (by simpa using H.mul_mem (H.inv_mem k.2) h)
    rw [dite_eq_right h2, dite_eq_right hy]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_loc {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {k : finU (E := E) (n := n)} (hk : k ∈ globLev S K')
    {w : Pl E} (hw : w ∈ S) : ∃ k' : UL n w, k' ∈ K' w ∧ (k' : GLw n w) = cLoc w k.1 := by
  unfold globLev at hk
  have := (Subgroup.mem_iInf.1 hk w)
  have := Subgroup.mem_iInf.1 this hw
  simpa using this

theorem globFn_mul_right {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ w, IsHecke (K' w) (f w)) {k : finU (E := E) (n := n)} (hk : k ∈ globLev S K') (x : finU (E := E) (n := n)) :
    globFn S f (x * k) = globFn S f x := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  obtain ⟨k', hk', he⟩ := mem_loc hk hw
  rw [Subgroup.coe_mul, map_mul, ← he]
  exact toSub_mul_right _ (K' w) (f w) (fun k hk x => ((hf w).2 k hk x).2) _ k' hk'

theorem globFn_mul_left {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ w, IsHecke (K' w) (f w)) {k : finU (E := E) (n := n)} (hk : k ∈ globLev S K') (x : finU (E := E) (n := n)) :
    globFn S f (k * x) = globFn S f x := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  obtain ⟨k', hk', he⟩ := mem_loc hk hw
  rw [Subgroup.coe_mul, map_mul, ← he]
  exact toSub_mul_left _ (K' w) (f w) (fun k hk x => ((hf w).2 k hk x).1) _ k' hk'

end GlobalTheory.BCT.TrKer.HopStab

namespace GlobalTheory.BCT.TrKer.HopStab
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem hopM_apply {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
    (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam))
    (hfin : (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' =>
      globFn S f q.out • (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id)).Finite)
    (x : finU (E := E) (n := n)) :
    hopM S lam K' f F x = (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ •
      ∑ᶠ q : finU (E := E) (n := n) ⧸ globLev S K', globFn S f q.out • F (x * q.out) := by
  have hsub : (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' => globFn S f q.out • F (x * q.out)) ⊆
      (hfin.toFinset : Set _) := by
    intro q hq
    simp only [Set.Finite.coe_toFinset, Function.mem_support] at hq ⊢
    intro h0
    apply hq
    have := congrArg (fun L : (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) => L F x) h0
    simpa [rightReg, LinearMap.funLeft] using this
  unfold hopM levOp
  rw [finsum_eq_sum _ hfin, finsum_eq_sum_of_support_subset _ hsub]
  simp [rightReg, LinearMap.funLeft, Finset.sum_apply, LinearMap.sum_apply]

end GlobalTheory.BCT.TrKer.HopStab

namespace GlobalTheory.BCT.TrKer.HopStab

theorem hopM_mem_vecM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E))
    (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ,
    IsTest (KL n) K' f → ∀ F ∈ vecM S lam K', hopM S lam K' f F ∈ vecM S lam K' := by
  intro E _ _ _ n S lam K' _ f hf F hF
  by_cases hfin : (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' =>
      globFn S f q.out • (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id)).Finite
  swap
  · have h0 : hopM S lam K' f = 0 := by
      unfold hopM levOp
      rw [finsum_of_infinite_support hfin, smul_zero]
    rw [h0]
    exact (vecM S lam K').zero_mem
  have hsupp : ∀ y : finU (E := E) (n := n), (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' =>
      globFn S f q.out • F (y * q.out)).Finite := by
    intro y
    refine hfin.subset fun q hq => ?_
    simp only [Function.mem_support] at hq ⊢
    intro h0
    apply hq
    have := congrArg (fun L : (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) => L F y) h0
    simpa [rightReg, LinearMap.funLeft] using this
  refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
  · rw [hopM_apply f F hfin, hopM_apply f F hfin, map_smul, map_finsum _ (hsupp x)]
    congr 1
    refine finsum_congr fun q => ?_
    rw [mul_assoc, hF.1 γ, map_smul]
  · rw [hopM_apply f F hfin, hopM_apply f F hfin]
    congr 1
    symm
    rw [← finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (finU (E := E) (n := n) ⧸ globLev S K'))]
    refine finsum_congr fun q => ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (globLev S K') (k * q.out)
    have hq : (MulAction.toPerm k : Equiv.Perm (finU (E := E) (n := n) ⧸ globLev S K')) q =
        ((k * q.out : finU (E := E) (n := n)) : finU (E := E) (n := n) ⧸ globLev S K') := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, hh, globFn_mul_right hf.1 h.2, globFn_mul_left hf.1 hk, ← mul_assoc, ← mul_assoc, hF.2 h h.2]

end GlobalTheory.BCT.TrKer.HopStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairPartnerInverseTranspose
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilPairPartner

theorem map_mul_map_inv {R S : Type} [Field R] [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (h : M.det ≠ 0) : M.map f * (M⁻¹).map f = 1 := by
  rw [← Matrix.map_mul, M.mul_nonsing_inv (isUnit_iff_ne_zero.mpr h), Matrix.map_one _ f.map_zero f.map_one]

theorem map_inv_mul_map {R S : Type} [Field R] [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (h : M.det ≠ 0) : (M⁻¹).map f * M.map f = 1 := by
  rw [← Matrix.map_mul, M.nonsing_inv_mul (isUnit_iff_ne_zero.mpr h), Matrix.map_one _ f.map_zero f.map_one]

theorem map_smul_eq {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m n : Type} (r : R) (M : Matrix m n R) :
    (r • M).map f = f r • M.map f := by
  ext i j
  simp

theorem conj_inv_transpose {S : Type} [CommRing S] (c : S →+* S) {n : Type} [Fintype n] [DecidableEq n] (ξ u : S)
    (hu : IsUnit u) (B Bi K G N : Matrix n n S) (hb : Bᵀ * K * B.map c = K) (hBB : B * Bi = 1) (hBB' : Bi * B = 1)
    (hK : ξ • K = u • N) (hGN : G * N = 1) (hNG : N * G = 1) : Bi.map c * G * Biᵀ = G := by
  have hbN : Bᵀ * N * B.map c = N := by
    have h1 : Bᵀ * (ξ • K) * B.map c = ξ • K := by rw [Matrix.mul_smul, Matrix.smul_mul, hb]
    rw [hK, Matrix.mul_smul, Matrix.smul_mul] at h1
    exact hu.smul_left_cancel.mp h1
  have hcc : Bi.map c * B.map c = 1 := by
    rw [← Matrix.map_mul, hBB', Matrix.map_one _ c.map_zero c.map_one]
  have hTT : Biᵀ * Bᵀ = 1 := by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  calc Bi.map c * G * Biᵀ = Bi.map c * G * Biᵀ * (N * G) := by rw [hNG, Matrix.mul_one]
    _ = Bi.map c * G * Biᵀ * ((Bᵀ * N * B.map c) * G) := by rw [hbN]
    _ = Bi.map c * G * (Biᵀ * Bᵀ) * N * B.map c * G := by simp only [Matrix.mul_assoc]
    _ = Bi.map c * (G * N) * B.map c * G := by rw [hTT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = G := by rw [hGN, Matrix.mul_one, hcc, Matrix.one_mul]

theorem pair_partner : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
      (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)),
      ∃ (g : GA D S) (h : GA D T), mt T h = a.1.1 ∧ mt S g = (b⁻¹).1.1ᵀ := by
  intro D S T JA JB ξ hA hB a b
  have hmap : ∀ {m n : Type} (X : Matrix m n (AE D)),
      X.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) = X.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) :=
    fun X => Matrix.ext fun i j => rfl

  have ha : (a.1.val)ᵀ * incM D.host.F JA * (a.1.val).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JA := a.2
  set A : Matrix (Fin T.rank) (Fin T.rank) (AE D) := a.1.val with hAdef
  have hJA : incM D.host.F JA = (incM D.host.F T.gram)ᵀ := by
    rw [hA]; rfl
  rw [hJA] at ha
  have ha' := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at ha'
  have hmemA : a.1 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig T.gram := by
    show Formalism.UG.cT _ a.1.val * _ * a.1.val = _
    simp only [Formalism.UG.cT, hmap]
    rw [Matrix.mul_assoc]
    exact ha'

  obtain ⟨cR, hcR⟩ : ∃ f, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig = f := ⟨_, rfl⟩
  have hb : (b.1.val)ᵀ * incM D.host.F JB * (b.1.val).map cR = incM D.host.F JB := by
    rw [← hcR, hmap]; exact b.2
  have hBB : b.1.val * (b⁻¹).1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).mul_inv
  have hBB' : (b⁻¹).1.val * b.1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).inv_mul
  obtain ⟨B, hBdef⟩ : ∃ B : Matrix (Fin S.rank) (Fin S.rank) (AE D), b.1.val = B := ⟨_, rfl⟩
  obtain ⟨Bi, hBidef⟩ : ∃ B : Matrix (Fin S.rank) (Fin S.rank) (AE D), (b⁻¹).1.val = B := ⟨_, rfl⟩
  rw [hBdef] at hb hBB hBB'
  rw [hBidef] at hBB hBB'
  have hGN := GlobalTheory.WeilPairPartner.map_mul_map_inv (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) S.gram
    (GlobalTheory.VolHeckeCompare.gram_det_ne_zero S)
  have hNG := GlobalTheory.WeilPairPartner.map_inv_mul_map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) S.gram
    (GlobalTheory.VolHeckeCompare.gram_det_ne_zero S)
  have hsm : incM D.host.F (D.host.xi0 • S.gram⁻¹) = inclR (F := D.host.F) (AF D.host.F) D.host.xi0 •
      incM D.host.F S.gram⁻¹ :=
    GlobalTheory.WeilPairPartner.map_smul_eq _ _ _
  have hu : IsUnit (inclR (F := D.host.F) (AF D.host.F) D.host.xi0) :=
    (isUnit_iff_ne_zero.mpr (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _
  have hcore := GlobalTheory.WeilPairPartner.conj_inv_transpose cR ξ _ hu B Bi (incM D.host.F JB) (incM D.host.F S.gram)
    (incM D.host.F S.gram⁻¹) hb hBB hBB' (hB.trans hsm) hGN hNG
  have hTT : Biᵀ * Bᵀ = 1 := by
    rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  let gU : GL (Fin S.rank) (AE D) :=
    ⟨Biᵀ, Bᵀ, hTT, by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩
  have hmemB : gU ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig S.gram := by
    show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) Biᵀ * incM D.host.F S.gram * Biᵀ =
      incM D.host.F S.gram
    rw [hcR]
    simp only [Formalism.UG.cT, Matrix.transpose_map, Matrix.transpose_transpose]
    exact hcore
  refine ⟨⟨gU, hmemB⟩, ⟨a.1, hmemA⟩, rfl, ?_⟩
  show Biᵀ = ((b⁻¹).1.val)ᵀ
  rw [hBidef]

end GlobalTheory.WeilPairPartner
end

