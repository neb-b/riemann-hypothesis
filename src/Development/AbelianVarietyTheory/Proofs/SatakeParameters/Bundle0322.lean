module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0039
public import GroundTheory.GlobalFields.NormResidueSymbol.Bundle0002
public import GroundTheory.GlobalFields.IdeleGroups.LocalNormGroups
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsWeight
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

namespace GlobalTheory.PolarizedWeight

theorem exists_isWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∃ wt : ℤ, IsWeight π wt := by
  intro E _ _ _ l a ha π χ h
  obtain ⟨hreg, hpol, -⟩ := h
  have hcomm : ∀ (τ : E →+* ℂ) (u : ℂ) (o : Op E a), Commute (cap (a := a) τ u) (act o) := fun τ u o => by
    cases o with
    | fin k => exact commute_cap_finRep τ u k
    | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
    | lie X => exact commute_cap_lie τ u X
  have hm : ∀ σ, π.HasInfChar σ ((CG.mk π).infChar σ) := fun σ =>
    GlobalTheory.CuspRep.hasInfChar_infChar_of_commute E a hcomm (CG.mk π) σ
  set ψ := GlobalTheory.GalOfCusp.compNorm E χ with hψ
  have key : ∀ τ : E →+* ℂ, (CG.mk π).infChar (ComplexEmbedding.conjugate τ) =
      ((CG.mk π).infChar τ).map fun z => -(z + expo ψ⁻¹ τ) := fun τ => by
    have h1 := (hm τ).twist ψ⁻¹
    rw [_root_.GlobalTheory.CapPair.infChar_conj_of_paired E a (π.twist ψ⁻¹) π hpol.dual τ _ _ h1 (hm (ComplexEmbedding.conjugate τ)), Multiset.map_map]
    rfl

  have hint : ∀ τ : E →+* ℂ, ∃ k : ℤ, expo ψ τ = k := fun τ => by
    obtain ⟨z, hz⟩ : ∃ z, z ∈ (CG.mk π).infChar τ :=
      Multiset.card_pos_iff_exists_mem.1 (by rw [(hm τ).1]; omega)
    obtain ⟨n, hn⟩ := (hreg τ).2 z hz
    have hz' : -(z + expo ψ⁻¹ τ) ∈ (CG.mk π).infChar (ComplexEmbedding.conjugate τ) := by
      rw [key]
      exact Multiset.mem_map.2 ⟨z, hz, rfl⟩
    obtain ⟨n', hn'⟩ := (hreg _).2 _ hz'
    refine ⟨n + n' + ((a : ℤ) - 1), ?_⟩
    rw [GlobalTheory.RegAlgCharAlg.expo_inv'] at hn'
    push_cast
    linear_combination hn' + hn
  choose k hk using hint
  have hkc : ∀ τ, k (ComplexEmbedding.conjugate τ) = k τ := fun τ => by
    have := (hk _).symm.trans ((_root_.GlobalTheory.NormExpo.expo_compNorm_conjugate E χ τ).trans (hk τ))
    exact_mod_cast this
  let n : (maximalRealSubfield E →+* ℂ) → ℤ := fun φ => k (ComplexEmbedding.lift E φ)
  have hkn : ∀ τ : E →+* ℂ, k τ = n (τ.comp (algebraMap (maximalRealSubfield E) E)) := fun τ => by
    rcases GlobalTheory.cm_eq_or_conj_of_comp_eq E (ComplexEmbedding.lift E (τ.comp (algebraMap (maximalRealSubfield E) E))) τ
      (ComplexEmbedding.lift_comp_algebraMap E _).symm with h | h
    · exact congrArg k h
    · exact (congrArg k h).trans (hkc _)

  have hn : ∀ g : (maximalRealSubfield E →+* ℂ) → ℂ,
      ∏ τ : E →+* ℂ, g (τ.comp (algebraMap (maximalRealSubfield E) E)) ^ k τ = ∏ φ, g φ ^ (2 * n φ) := by
    classical
    intro g
    rw [← Finset.prod_fiberwise Finset.univ
      (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E))]
    refine Finset.prod_congr rfl fun φ _ => ?_
    set τ₀ := ComplexEmbedding.lift E φ with hτ₀
    have h0 : τ₀.comp (algebraMap (maximalRealSubfield E) E) = φ :=
      ComplexEmbedding.lift_comp_algebraMap E φ
    have h1 : (ComplexEmbedding.conjugate τ₀).comp (algebraMap (maximalRealSubfield E) E) = φ := by
      rw [GlobalTheory.cm_conj_comp_eq, h0]
    have hne : τ₀ ≠ ComplexEmbedding.conjugate τ₀ := fun h =>
      IsTotallyComplex.complexEmbedding_not_isReal τ₀ (ComplexEmbedding.isReal_iff.2 h.symm)
    have hfib : Finset.univ.filter
        (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E) = φ) =
        {τ₀, ComplexEmbedding.conjugate τ₀} := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h
        exact GlobalTheory.cm_eq_or_conj_of_comp_eq E τ₀ τ (h.trans h0.symm)
      · rintro (rfl | rfl)
        · exact h0
        · exact h1
    rw [hfib, Finset.prod_pair hne, h0, h1, hkc, mul_comm (2 : ℤ), zpow_mul, zpow_two]
  have hAlg : IsAlgPos χ n := fun x hx => by
    have hpos : ∀ φ : maximalRealSubfield E →+* ℂ,
        ((‖φ (x : maximalRealSubfield E)‖ : ℝ) : ℂ) = φ x ∧ 0 < ‖φ (x : maximalRealSubfield E)‖ := by
      intro φ
      have hr : ComplexEmbedding.IsReal φ := InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
      have h0 := hx hr.embedding
      rw [← hr.coe_embedding_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]
      exact ⟨rfl, h0⟩
    let z : Cinf E := fun w => ((Real.log (w ((x : maximalRealSubfield E) : E)) / 2 : ℝ) : ℂ)
    let u : (Cinf E)ˣ := expU z
    have hu : u * Units.map (starRingEnd (Cinf E)).toMonoidHom u =
        Units.map (diagInf E).toMonoidHom (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom x) := by
      apply Units.ext
      funext w
      have e1 := hpos (w.embedding.comp (algebraMap _ E))
      have e2 : ‖w.embedding ((x : maximalRealSubfield E) : E)‖ = w ((x : maximalRealSubfield E) : E) :=
        InfinitePlace.norm_embedding_eq w _
      change Complex.exp (z w) * starRingEnd ℂ (Complex.exp (z w)) = pInf E (algebraMap E (Ad E) ((x : maximalRealSubfield E) : E)) w
      rw [pInf_algebraMap, ← Complex.exp_conj, Complex.conj_ofReal, ← Complex.exp_add, ← Complex.ofReal_add,
        ← Complex.ofReal_exp, show Real.log (w ((x : maximalRealSubfield E) : E)) / 2 + Real.log (w ((x : maximalRealSubfield E) : E)) / 2 =
          Real.log (w ((x : maximalRealSubfield E) : E)) by ring, Real.exp_log (e2 ▸ e1.2), ← e2]
      exact e1.1
    have hN : ideleNorm E (infId E u) = infDiag x := _root_.GlobalTheory.IdeleMapInjective.ideleMap_injective E (by rw [_root_.GlobalTheory.GalReal.ideleMap_ideleNorm_infId, hu, ← InfType.infDiag_eq, _root_.GlobalTheory.InfDiagExt.ideleMap_infDiag])
    have e1 : ((χ.inf x : ℂˣ) : ℂ) = ((chiInf (compNorm E χ) u : ℂˣ) : ℂ) := by
      rw [HChar.inf, MonoidHom.comp_apply, ← hN]; rfl
    rw [e1, chiInf_eq_prod _ k hk]
    let g : (maximalRealSubfield E →+* ℂ) → ℂ := fun φ =>
      Complex.exp ((Real.log ‖φ (x : maximalRealSubfield E)‖ / 2 : ℝ) : ℂ)
    have hc : ∀ τ : E →+* ℂ, coord τ (u : Cinf E) = g (τ.comp (algebraMap _ E)) := by
      intro τ
      rw [coord_expU]
      congr 1
      have e3 : z (InfinitePlace.mk τ) = ((Real.log ‖(τ.comp (algebraMap (maximalRealSubfield E) E)) (x : maximalRealSubfield E)‖ / 2 : ℝ) : ℂ) := by
        simp only [z, InfinitePlace.apply]; rfl
      unfold coord
      split_ifs
      · exact e3
      · change starRingEnd ℂ (z (InfinitePlace.mk τ)) = _
        rw [e3, Complex.conj_ofReal]
    simp only [hc]
    rw [hn g]
    refine Finset.prod_congr rfl fun φ _ => ?_
    rw [zpow_mul, zpow_two, ← Complex.exp_add, ← Complex.ofReal_add, ← Complex.ofReal_exp,
      show Real.log ‖φ (x : maximalRealSubfield E)‖ / 2 + Real.log ‖φ (x : maximalRealSubfield E)‖ / 2 =
        Real.log ‖φ (x : maximalRealSubfield E)‖ by ring, Real.exp_log (hpos φ).2, (hpos φ).1]
  have hpar := UpperTheory.heckeChar_parallel_weight (maximalRealSubfield E) χ n hAlg
  obtain ⟨φ₀⟩ : Nonempty (maximalRealSubfield E →+* ℂ) := inferInstance
  refine ⟨(a : ℤ) - 1 - n φ₀, fun τ => ?_⟩
  have hconj : τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom = ComplexEmbedding.conjugate τ := by
    ext x
    exact IsCMField.complexEmbedding_complexConj E τ x
  have hb : expo ψ⁻¹ τ = -(n φ₀ : ℂ) := by
    rw [GlobalTheory.RegAlgCharAlg.expo_inv', hk, hkn, hpar _ φ₀]
  rw [hconj, key]
  refine Multiset.map_congr rfl fun z _ => ?_
  rw [hb]
  push_cast
  ring

end GlobalTheory.PolarizedWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GmOfMapEqActC
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK Formalism.MainNotions.G.GAtP.algOK

theorem blk_frame_eq {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)
    (hT : PosTie X D pos Kc ι ρ) (fd : FData X D) (j : ℕ) (La : X.Lt j) {n : ℕ} (h : (X.Pj j).m + 1 = n)
    (M : GL (Fin n) D.host.E) (hU : StdU D M) (hF : FrIs fd ρ j La h M) :
    (fun v s => Matrix.GeneralLinearGroup.map (algebraMap X.G.Kf Kc)
        (gPosGL (X.Pj j) v s ((SecondKernelHermitian.glInv X j (SecondKernelHermitian.BOf fd j La) v)⁻¹))) =
      (fun v s => Matrix.GeneralLinearGroup.map ι (hAt (X.Pj j) h (posJ X D pos j) (fun _ => 1) (atR D M) v s)) := by
  have hblk := _root_.GlobalTheory.TwV.DelA.blkC_atR_read X D pos Kc ι ρ hT M hU
  cases j with
  | zero =>
    funext (v : X.Pl) (s : Fin (X.G.P.n' v))
    have hA : (SecondKernelHermitian.glInv X 0 (SecondKernelHermitian.BOf fd 0 La) v)⁻¹ = SecondKernelHermitian.frGL fd 0 La v := inv_inv _
    have hdet : IsUnit (fd.frM 0 La v).det := by
      rw [hF v, Matrix.det_submatrix_equiv_self]
      have hu := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).map (ρ v)
      rw [RingHom.map_det] at hu
      exact hu
    have hv : (SecondKernelHermitian.frGL fd 0 La v : Matrix _ _ _) = fd.frM 0 La v := by
      unfold SecondKernelHermitian.frGL
      rw [dite_eq_left hdet]
      rfl
    apply Units.ext
    ext a b
    have e1 := congrFun (congrFun (hblk v s).1 (finCongr h a)) (finCongr h b)
    simp only [Matrix.map_apply] at e1
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, hA]
    show algebraMap X.G.Kf Kc (X.G.P.ι v ((X.G.P.σ v ^ s.val) ((SecondKernelHermitian.frGL fd 0 La v : Matrix _ _ _) a b))) = _
    rw [hv, hF v]
    by_cases hs : Even s.val
    · have ho : ¬ IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact not_not.2 hs
      rw [if_neg ho] at e1
      simp only [hAt, hs, if_true]
      rw [one_mul, inv_one, mul_one]
      exact e1.symm
    · have ho : IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact hs
      rw [if_pos ho] at e1
      simp only [hAt, hs, if_false, invT]
      rw [one_mul, inv_one, mul_one, ← map_inv]
      exact e1.symm
  | succ j =>
    funext (v : X.Pl) (s : Fin (X.G.P.n' v))
    have hA : (SecondKernelHermitian.glInv X (j + 1) (SecondKernelHermitian.BOf fd (j + 1) La) v)⁻¹ = SecondKernelHermitian.frGL fd (j + 1) La v := inv_inv _
    have hdet : IsUnit (fd.frM (j + 1) La v).det := by
      rw [hF v, Matrix.det_submatrix_equiv_self]
      have hu := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).map (ρ v)
      rw [RingHom.map_det] at hu
      exact hu
    have hv : (SecondKernelHermitian.frGL fd (j + 1) La v : Matrix _ _ _) = fd.frM (j + 1) La v := by
      unfold SecondKernelHermitian.frGL
      rw [dite_eq_left hdet]
      rfl
    apply Units.ext
    ext a b
    have e1 := congrFun (congrFun (hblk v s).1 (finCongr h a)) (finCongr h b)
    simp only [Matrix.map_apply] at e1
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, hA]
    show algebraMap X.G.Kf Kc (X.G.P.ι v ((X.G.P.σ v ^ s.val) ((SecondKernelHermitian.frGL fd (j + 1) La v : Matrix _ _ _) a b))) = _
    rw [hv, hF v]
    by_cases hs : Even s.val
    · have ho : ¬ IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact not_not.2 hs
      rw [if_neg ho] at e1
      simp only [hAt, hs, if_true]
      rw [one_mul, inv_one, mul_one]
      exact e1.symm
    · have ho : IsOddPos s := by
        unfold IsOddPos; rw [← Nat.odd_iff, ← Nat.not_even_iff_odd]; exact hs
      rw [if_pos ho] at e1
      simp only [hAt, hs, if_false, invT]
      rw [one_mul, inv_one, mul_one, ← map_inv]
      exact e1.symm

end GlobalTheory.TwV.DelA

namespace GlobalTheory.TwV.DelA

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK Formalism.MainNotions.G.GAtP.algOK

theorem gmOf_map_eq_actC : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (La : X.Lt j) {n : ℕ} (h : (X.Pj j).m + 1 = n) (M : GL (Fin n) D.host.E), StdU D M → FrIs fd ρ j La h M → ∀ (G : (X.Pj j).Xsp) (V : XR (X.Pj j) ℂ), MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι V → MvPolynomial.map (algebraMap X.G.Kf Kc) (gmOf fd j La G) = MvPolynomial.map ι (actC X D pos j h M V) := by
  intro p _ X D pos Kc _ _ ι ρ hT fd j La n h M hU hF G V hGV
  unfold gmOf actC
  rw [natAct_eq, map_natActR, map_natActR, ← hGV, blk_frame_eq X D pos Kc ι ρ hT fd j La h M hU hF]

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtOfSphericalAndTwistSpherical
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.SphTwistUnr

open GlobalTheory.PRep

theorem map_mem_twKer {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
    (S : V →ₗ[ℂ] V) (hS : ∀ h, S ∘ₗ ρ h = ρ h ∘ₗ S) {v : V} (hv : v ∈ twKer ρ K 1) : S v ∈ twKer ρ K 1 := by
  have h : (twKer ρ K 1).map S ≤ twKer ρ K 1 := by
    rw [twKer, Submodule.map_span_le]
    rintro _ ⟨n, u, rfl⟩
    refine Submodule.subset_span ⟨n, S u, ?_⟩
    have := LinearMap.congr_fun (hS n) u
    simp only [LinearMap.comp_apply] at this
    simp [this]
  exact h ⟨v, hv, rfl⟩

theorem unrAt_of_isSpherical_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ξ).locRep w) (GlobalTheory.LFun.KGL w (n := a)) → ξ.UnrAt w := by
  intro E _ _ _ a ha π ξ w hB hsph
  obtain ⟨B, hB⟩ := hB
  have hS : GlobalTheory.LFun.HasSatGL w (π.locRep w) B := (CG.hasSat_mk π w B).1 hB
  have hK : IsCompact ((GlobalTheory.LFun.KGL w (n := a) : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2
  have hsm : IsSmooth (π.locRep w) := π.isSmooth_locRep w
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hS.1
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).1 hsph
  have hT : ∀ g v, (π.twist ξ).locRep w g (π.toTwist ξ v) =
      ((ξ.loc w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • π.toTwist ξ (π.locRep w g v) := by
    intro g v
    rw [CuspSub.locRep_eq, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, CuspSub.chiDet_locGL]
    rfl
  obtain ⟨y, rfl⟩ := (π.toTwist ξ).surjective z
  have hy0 : y ≠ 0 := fun h => hz0 (by rw [h]; exact (π.toTwist ξ).toLinearMap.map_zero)
  have hy : ∀ k ∈ GlobalTheory.LFun.KGL w (n := a), π.locRep w k y =
      (((ξ.loc w (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) • y := by
    intro k hk
    have h1 := GlobalTheory.LGrp.mem_fixed.1 hz k hk
    rw [hT] at h1
    apply (π.toTwist ξ).injective
    rw [map_smul, ← h1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  by_contra hne
  obtain ⟨u, hu, hξu⟩ : ∃ u, Formalism.L2.Host.IsUnitAt w u ∧ ξ.loc w u ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne h
  have hall := GlobalTheory.T.translate_mem_twistedJacquetKernel_ramified E w a π.V (π.locRep w) (ξ.loc w) u ha hu hξu y hy
  let Wl : Submodule ℂ π.V := ⨅ g, (twKer (π.locRep w) (GlobalTheory.LFun.KGL w (n := a)) 1).comap (π.locRep w g)
  have memWl : ∀ v, v ∈ Wl ↔ ∀ g, π.locRep w g v ∈ twKer (π.locRep w) (GlobalTheory.LFun.KGL w (n := a)) 1 := fun v => by
    simp [Wl, Submodule.mem_iInf]
  have stab : GlobalTheory.CuspRep.IsStable (Wl.map π.V.subtype) := by
    rintro o _ ⟨v, hv, rfl⟩
    obtain ⟨g, S, hS, ho⟩ := _root_.GlobalTheory.LocFactor.exists_locRep_comp E a π w o
    have hv' := (memWl v).1 hv
    refine ⟨π.op o v, (memWl _).2 fun h => ?_, rfl⟩
    rw [ho, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul]
    have e := LinearMap.congr_fun (hS (h * g)) v
    simp only [LinearMap.comp_apply] at e
    rw [← e]
    exact map_mem_twKer S hS (hv' (h * g))
  rcases π.irred _ (Submodule.map_subtype_le _ _) stab with h | h
  · have h1 : (y : GlobalTheory.CuspRep.Sm E a) ∈ Wl.map π.V.subtype := ⟨y, (memWl y).2 hall, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    exact hy0 (Subtype.ext h1)
  · have h1 : (x : GlobalTheory.CuspRep.Sm E a) ∈ Wl.map π.V.subtype := by rw [h]; exact x.2
    obtain ⟨x', hx', e⟩ := h1
    obtain rfl : x' = x := Subtype.ext e
    have h2 := (memWl x').1 hx' 1
    rw [map_one, Module.End.one_apply] at h2
    exact hx0 (Submodule.disjoint_def.1 (GlobalTheory.LocGL.isCompl_fixed_twKer hsm hK).disjoint x' hx h2)

end GlobalTheory.SphTwistUnr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtUnderOfCompNormUnramified
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section
open scoped GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal
namespace GlobalTheory.NormBelow
open GlobalTheory.UnitaryHeckeBaseChange

theorem ideleNorm_eq_found (E : Type) [Field E] [NumberField E] [IsCMField E] (x : (AdeleRing (𝓞 E) E)ˣ) :
    ideleNorm E x = GroundTheory.Global.ideleNorm (maximalRealSubfield E) E x := by
  apply Units.ext
  obtain ⟨z, hz⟩ := (adeleEquiv (isCMExt_real E)).surjective (x : AdeleRing (𝓞 E) E)
  have h : adeleNorm E (adeleEquiv (isCMExt_real E) z) = Algebra.norm _ z :=
    congrArg (Algebra.norm _) ((adeleEquiv (isCMExt_real E)).symm_apply_apply z)
  have h2 : ∀ z, toAdele (maximalRealSubfield E) E z =
      GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft (maximalRealSubfield E) E z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a l =>
      rw [toAdele_tmul, GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft_tmul]
      have hm : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap
          (maximalRealSubfield E) E = GroundTheory.Global.AdeleBaseChange.adeleMap
          (maximalRealSubfield E) E := by
        ext a : 1
        apply Prod.ext
        · funext w
          open scoped NumberField.LiesOver in
          change AbsoluteValue.Completion.map _ _ _ = algebraMap _ _ _
          rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver]
        · apply FiniteAdeleRing.ext
          intro w
          change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap _ _ w _ =
            GroundTheory.Global.SemiLocal.completionMap _ w _
          rfl
      rw [hm, mul_comm]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  change adeleNorm E (x : AdeleRing (𝓞 E) E) = _
  rw [GroundTheory.Global.coe_ideleNorm, ← hz, h]
  have h3 : adeleEquiv (isCMExt_real E) z = _ := h2 z
  rw [h3]
  exact (Algebra.norm_eq_of_algEquiv _ _).symm

theorem ideleNorm_localIdele (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E))
    (y : (w.adicCompletion E)ˣ) :
    ideleNorm E (localIdele E w y) = localIdele (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E)))
      (GroundTheory.LocalField.normUnits _ (w.adicCompletion E) y) := by
  rw [ideleNorm_eq_found]
  exact GroundTheory.Global.ideleNorm_finiteEmbedding (K := maximalRealSubfield E) w y

end GlobalTheory.NormBelow

namespace GlobalTheory.NormBelow
open GlobalTheory.UnitaryHeckeBaseChange

theorem unrAt_under_of_compNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (χ : HChar (maximalRealSubfield E)) (w : HeightOneSpectrum (𝓞 E)), ¬ GlobalTheory.UnitaryBC.IsSplitAt w →
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → (compNorm E χ).UnrAt w →
    χ.UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  intro E _ _ _ χ w _ hur hχ x hx
  have he : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 :=
    Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 (maximalRealSubfield E))
  haveI : w.asIdeal.LiesOver (w.under (𝓞 (maximalRealSubfield E))).asIdeal := ⟨rfl⟩
  have hxm : x ∈ (Submonoid.ofClass ((w.under (𝓞 (maximalRealSubfield E))).adicCompletionIntegers
      (maximalRealSubfield E))).units := by
    unfold IsUnitAt at hx
    refine (Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx.le
    · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  obtain ⟨y, hy, hyn⟩ := GroundTheory.Global.IdeleNorm.exists_norm_eq_of_ramificationIdx_eq_one _ w he hxm
  have hyu : IsUnitAt w y := by
    obtain ⟨h1, h2⟩ := (Submonoid.mem_units_iff _ _).1 hy
    have h1' := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1
    have h2' := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h2
    unfold IsUnitAt
    refine le_antisymm h1' ?_
    have e : Valued.v (y : w.adicCompletion E) * Valued.v ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc (1 : _) = _ := e.symm
      _ ≤ Valued.v (y : w.adicCompletion E) := mul_le_of_le_one_right' h2'
  have key : χ.loc (w.under (𝓞 (maximalRealSubfield E))) x = (compNorm E χ).loc w y := by
    show χ.1 (localIdele _ _ x) = χ.1 (ideleNorm E (localIdele E w y))
    rw [ideleNorm_localIdele]
    congr 2
    apply Units.ext
    rw [GroundTheory.LocalField.coe_normUnits]
    exact hyn.symm
  rw [key]
  exact hχ y hyu

end GlobalTheory.NormBelow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialCoeffsWeightExtendedByZeroStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorPolynomial_coeffs_weight_extended_by_zero : ∀ (D : D7) {N N' : ℕ}, N ≤ N' → ∀ (s : D.what₂.Tau → ℂ) (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ), Q ∈ WtPol ℂ ν → (∀ α, AddMonoidAlgebra.coeff (polDY D s Q (N' := N')) α ∈ WtPol ℂ (extNu N' ν)) ∧ ∀ Θ : TaylorLogMetric.VC D N N' → ℂ, framePol D s Q Θ ∈ WtPol ℂ (extNu N' ν) := by
  first | exact @GlobalTheory.TwV.DelA.wt_polDY_framePol | exact GlobalTheory.TwV.DelA.wt_polDY_framePol | (intros; apply GlobalTheory.TwV.DelA.wt_polDY_framePol <;> assumption)
end

