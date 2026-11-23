module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumCoordinateIsAlgebraic
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.ToricCoordAlg

theorem isAlgebraic_coordIn : ∀ (hA : LatAlg) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ)
    (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ : IsLatOf ι 1 Λ₀)
    (hΩ : Ω₀ ^ 12 = latDisc Λ₀) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s)
    (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ)
    (hV : IsValSum φ s κ 𝔣 Q χ T), IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := by
  intro hA K _ _ d δ ι h2 hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q χ T hV
  classical
  obtain ⟨hQ, hχ, hfin, S, hS, rfl⟩ := hV
  have htriv := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 Q χ hE h𝔣 hQ hχ
  have : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, GlobalTheory.TwistedTransportProof.coordIn_eq, Finset.mul_sum]
  refine (mem_algebraicClosure_iff (F := ℚ) (E := ℂ)).1 (sum_mem fun q _ => ?_)
  have e : coordIn E d s κ Ω₀ 1 * (((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * S q 0) =
      ((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * coordIn E d s κ Ω₀ (S q 0) := by
    rw [GlobalTheory.TwistedTransportProof.coordIn_eq d s κ Ω₀ (S q 0)]; ring
  rw [e]
  have h1 := hA K d δ ι h2 hd hδ Λ₀ Ω₀ hΛ hΩ E I φ s 𝔣 Q ⟨hE, hφ, hφK, hs, h𝔣, hQ⟩ κ q.out (S q) (hS q)
  have h3 : IsAlgebraic ℚ ((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ)) :=
    (GlobalTheory.ToricRatioBridge.isAlgebraic_finPart hχ.2.2.1 htriv q.out).mul
      (GlobalTheory.TwistedTransportProof.isAlgebraic_modF_pow q.out s)
  refine mul_mem (inv_mem ?_) ?_ <;> rw [mem_algebraicClosure_iff] <;> assumption

end GlobalTheory.ToricCoordAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjOfTwistedNormEqGLOneUnramified
section
open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct

namespace GlobalTheory.LKMid

theorem twistedNormProductIterate_map_intertwining {H H' : Type} [Group H] [Group H'] (θ : H →* H) (θ' : H' →* H') (f : H →* H')
    (hf : ∀ x, f (θ x) = θ' (f x)) (r : ℕ) (x : H) : f (nrmG θ r x) = nrmG θ' r (f x) := by
  unfold nrmG
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (Function.Semiconj.iterate_right (f := f) (ga := θ) (gb := θ') hf i) x

theorem twistedNormProductIterate_mul_commGroup {H : Type} [CommGroup H] (θ : H →* H) (r : ℕ) (a b : H) :
    nrmG θ r (a * b) = nrmG θ r a * nrmG θ r b := by
  unfold nrmG
  rw [← List.prod_map_mul]
  congr 1
  apply List.map_congr_left
  intro i hi
  clear hi
  induction i generalizing a b with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, map_mul, ih]

end GlobalTheory.LKMid

namespace GlobalTheory.LKMid

theorem det_unramifiedExtFrobeniusGLEntrywise_GL_one (p : ℕ) [Fact p.Prime] (r : ℕ) (x : GL (Fin 1) (Qr p r)) :
    Matrix.GeneralLinearGroup.det (GlobalTheory.LKLoc.sig p (Q0 p) 1 r x) =
      Units.map (frobQ p r).toRingHom.toMonoidHom (Matrix.GeneralLinearGroup.det x) := by
  ext
  simp [GlobalTheory.LKLoc.sig, Matrix.det_unique]
  rfl

theorem generalLinearGroup_det_injective_GL_one (R : Type) [CommRing R] :
    Function.Injective (Matrix.GeneralLinearGroup.det : GL (Fin 1) R →* Rˣ) := by
  intro x y h
  ext i j
  have := congrArg Units.val h
  simp [Matrix.det_unique] at this
  fin_cases i; fin_cases j
  exact this

theorem generalLinearGroup_det_scalar_GL_one (R : Type) [CommRing R] (u : Rˣ) :
    Matrix.GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) u) = u := by
  ext
  simp [Matrix.det_unique]

theorem exists_sig_twisted_conj_of_nrmG_eq : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ δ' : GL (Fin 1) (Qr p r),
    nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ = nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ' →
    ∃ h : GL (Fin 1) (Qr p r), δ' = h⁻¹ * δ * GlobalTheory.LKLoc.sig p (Q0 p) 1 r h := by
  intro p _ r hr δ δ' hN
  let D : GL (Fin 1) (Qr p r) →* (Qr p r)ˣ := Matrix.GeneralLinearGroup.det
  let θ : (Qr p r)ˣ →* (Qr p r)ˣ := Units.map (frobQ p r).toRingHom.toMonoidHom
  have hD : ∀ x, D (GlobalTheory.LKLoc.sig p (Q0 p) 1 r x) = θ (D x) := det_unramifiedExtFrobeniusGLEntrywise_GL_one p r
  have hN' : nrmG θ r (D δ) = nrmG θ r (D δ') := by
    rw [← twistedNormProductIterate_map_intertwining _ _ D hD, ← twistedNormProductIterate_map_intertwining _ _ D hD, hN]
  let c : (Qr p r)ˣ := D δ' * (D δ)⁻¹
  have hc : nrmG θ r c = 1 := by
    have h1 : nrmG θ r c * nrmG θ r (D δ) = nrmG θ r (D δ) := by
      rw [← twistedNormProductIterate_mul_commGroup, inv_mul_cancel_right, hN']
    exact mul_eq_right.1 h1
  let L := Algebra.TensorProduct.lid ℚ_[p] (Qr p r)
  let Φ := Algebra.TensorProduct.map (AlgHom.id ℚ_[p] ℚ_[p]) (frobQ p r)
  have hL : ∀ x, L (Φ x) = frobQ p r (L x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b y =>
      simp only [L, Φ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, AlgHom.id_apply]
      exact ((frobQ p r).toLinearMap.map_smul b y).symm
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  have hLs : ∀ y, L.symm (frobQ p r y) = Φ (L.symm y) := by
    intro y
    apply L.injective
    rw [hL, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  let fS : (Qr p r)ˣ →* (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ := Units.map L.symm.toAlgHom.toRingHom.toMonoidHom
  let fL : (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ →* (Qr p r)ˣ := Units.map L.toAlgHom.toRingHom.toMonoidHom
  let ΦU : (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ →* (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ := Units.map Φ.toRingHom.toMonoidHom
  have hfS : ∀ x, fS (θ x) = ΦU (fS x) := fun x => Units.ext (hLs x)
  have hfL : ∀ x, fL (ΦU x) = θ (fL x) := fun x => Units.ext (hL x)
  have hLS : ∀ x, fL (fS x) = x := fun x => Units.ext (AlgEquiv.apply_symm_apply L x)
  have ha : nrmG ΦU r (fS c) = 1 := by
    rw [← twistedNormProductIterate_map_intertwining _ _ fS hfS, hc, map_one]
  obtain ⟨g, hg⟩ := hilbert90_frobenius_tensor_unramified_padic p r hr ℚ_[p] (fS c) ha
  have hc' : c = (fL g)⁻¹ * θ (fL g) := by
    rw [← hLS c, hg, map_mul, map_inv, hfL]
  refine ⟨GeneralLinearGroup.scalar (Fin 1) (fL g), generalLinearGroup_det_injective_GL_one _ ?_⟩
  have hs : D (GeneralLinearGroup.scalar (Fin 1) (fL g)) = fL g := generalLinearGroup_det_scalar_GL_one _ _
  have e : D δ' = c * D δ := by rw [inv_mul_cancel_right]
  change D δ' = D ((GeneralLinearGroup.scalar (Fin 1) (fL g))⁻¹ * δ * GlobalTheory.LKLoc.sig p (Q0 p) 1 r (GeneralLinearGroup.scalar (Fin 1) (fL g)))
  rw [map_mul, map_mul, map_inv, hD, hs, e, hc']
  exact mul_right_comm _ _ _

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugatesAlgebraRelation
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.Div

theorem conj_of_twist : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (y₁ y₂ : grp G β) (y₀ c₁ c₂ w : G.Cˣ) (r : ℚ),
    (((y₁ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c₁ * y₀ * ((c₁⁻¹ : G.Cˣ) : G.C) →
    (((y₂ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c₂ * y₀ * ((c₂⁻¹ : G.Cˣ) : G.C) →
    (y₁ : G.Cˣ × ℚˣ).2 = (y₂ : G.Cˣ × ℚˣ).2 → Commute (w : G.C) y₀ → 0 < r →
    (((c₂⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₂⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C r * ((w : G.C) * (((c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₁⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * ((β : G.C) * sh G (w : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) →
    ∃ γ : grp G β, y₂ = γ * y₁ * γ⁻¹ := by
  intro p _ G β y₁ y₂ y₀ c₁ c₂ w r h1 h2 hs hw hr H
  have shm : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have shc : sh G ((c₂⁻¹ : G.Cˣ) : G.C) * sh G (c₂ : G.C) = 1 := by
    rw [← shm, Units.mul_inv]; simp [sh]
  have hR : algebraMap ℚ G.C r⁻¹ * algebraMap ℚ G.C r = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hr.ne', map_one]
  set ru : ℚˣ := Units.mk0 r hr.ne' with hru

  have HX : (w : G.C) * (((c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₁⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
      ((β : G.C) * sh G (w : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C r⁻¹ *
      (((c₂⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₂⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
    rw [H, ← mul_assoc (algebraMap ℚ G.C r⁻¹), hR, one_mul]
  have mem : ((c₂ * w * c₁⁻¹, ru⁻¹) : G.Cˣ × ℚˣ) ∈ grp G β := by
    refine ⟨?_, ?_⟩
    · change ((c₂ * w * c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₂ * w * c₁⁻¹ : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((ru⁻¹ : ℚˣ) : ℚ) * β
      rw [Units.val_inv_eq_inv_val, hru, Units.val_mk0]
      simp only [Units.val_mul, shm]
      calc (c₂ : G.C) * w * ((c₁⁻¹ : G.Cˣ) : G.C) * β * (sh G ((c₁⁻¹ : G.Cˣ) : G.C) * (sh G (w : G.C) * sh G (c₂ : G.C)))
          = c₂ * ((w : G.C) * (((c₁⁻¹ : G.Cˣ) : G.C) * β * sh G ((c₁⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
            ((β : G.C) * sh G (w : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) * β * sh G (c₂ : G.C) := by
            simp only [mul_assoc, Units.inv_mul_cancel_left]
        _ = algebraMap ℚ G.C r⁻¹ * ((c₂ : G.C) * ((c₂⁻¹ : G.Cˣ) : G.C) * β *
              (sh G ((c₂⁻¹ : G.Cˣ) : G.C) * sh G (c₂ : G.C))) := by
            rw [HX, Algebra.left_comm]
            simp only [mul_assoc, Units.inv_mul_cancel_left]
        _ = _ := by rw [shc, Units.mul_inv, one_mul, mul_one]
    · change 0 < ((ru⁻¹ : ℚˣ) : ℚ)
      rw [Units.val_inv_eq_inv_val, hru, Units.val_mk0]; exact inv_pos.2 hr
  refine ⟨⟨_, mem⟩, ?_⟩
  have e1 : (y₁ : G.Cˣ × ℚˣ).1 = c₁ * y₀ * c₁⁻¹ := Units.ext (by rw [h1]; simp)
  have e2 : (y₂ : G.Cˣ × ℚˣ).1 = c₂ * y₀ * c₂⁻¹ := Units.ext (by rw [h2]; simp)
  have hwu : w * y₀ = y₀ * w := Units.ext (by simpa using hw.eq)
  have hwu' : ∀ x : G.Cˣ, w * (y₀ * x) = y₀ * (w * x) := fun x => by rw [← mul_assoc, hwu, mul_assoc]
  apply Subtype.ext
  apply Prod.ext
  · show (y₂ : G.Cˣ × ℚˣ).1 = (c₂ * w * c₁⁻¹) * (y₁ : G.Cˣ × ℚˣ).1 * (c₂ * w * c₁⁻¹)⁻¹
    rw [e1, e2]
    simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, hwu', mul_inv_cancel_left]
  · show (y₂ : G.Cˣ × ℚˣ).2 = ru⁻¹ * (y₁ : G.Cˣ × ℚˣ).2 * ru⁻¹⁻¹
    rw [hs, mul_comm ru⁻¹, mul_assoc, mul_inv_cancel, mul_one]

end GlobalTheory.Div
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormProductIterateTwistedConjStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedNormProductIterate_twistedConj : ∀ {H : Type} [Group H] (θ : H →* H) (r : ℕ) (δ g : H), nrmG θ r (g⁻¹ * δ * θ g) = g⁻¹ * nrmG θ r δ * (⇑θ)^[r] g ∧ δ * θ (nrmG θ r δ) = nrmG θ r δ * (⇑θ)^[r] δ := by
  first | (exact @GlobalTheory.LKMid.nrmG_twConj) | (exact GlobalTheory.LKMid.nrmG_twConj) | (intros; apply GlobalTheory.LKMid.nrmG_twConj  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.UnitaryAdelicTop

theorem isClosed_UG {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [TopologicalSpace B] [IsTopologicalRing B]
    [T2Space B] (c : B →ₐ[A] B) (hc : Continuous c) {n : ℕ} (J : Matrix (Fin n) (Fin n) B) :
    IsClosed (UG c J : Set (GL (Fin n) B)) := by
  have hv : Continuous fun g : GL (Fin n) B => (g : Matrix (Fin n) (Fin n) B) := Units.continuous_val
  exact isClosed_eq (((hv.matrix_transpose).matrix_mul continuous_const).matrix_mul (hv.matrix_map hc)) continuous_const

theorem lcsc_UA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), IsTopologicalGroup (UA σ J) ∧ LocallyCompactSpace (UA σ J) ∧
      SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  intro F E _ _ _ _ _ σ n J
  haveI : IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := e.secondCountableTopology
  haveI : T2Space (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := Units.isEmbedding_embedProduct.t2Space
  have hσ : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc := isClosed_UG (cA σ) hσ (incM F J)
  exact ⟨inferInstance, hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology, inferInstance⟩

end GlobalTheory.UnitaryAdelicTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointExtOfComponents
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem finiteAdeleRingAway_eq_of_forall_eval_eq {p : ℕ} {x y : AfP p} (h : ∀ v : AwayP p, AfP.eval v x = AfP.eval v y) : x = y :=
  RestrictedProduct.ext (R := fun v : AwayP p => v.1.adicCompletion ℚ) _ h

theorem basV_repr_map {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (x : AfP p ⊗[ℚ] G.C)
    (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C) x) i =
      AfP.eval v ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [basV, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem ext_of_piV : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g g' : G.GAf),
    (∀ v : AwayP p, piV G v g = piV G v g') → g = g' := by
  intro p _ G g g' h
  have h1 : ∀ v : AwayP p, Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) =
      Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)
      (((g' : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) := fun v =>
    congrArg (fun z : Gv G v => (((z : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C))) (h v)
  have h2 : ∀ v : AwayP p, AfP.eval v (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p)) =
      AfP.eval v (((g' : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p)) := fun v =>
    congrArg (fun z : Gv G v => (((z : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : Qv v))) (h v)
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    apply (Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).ext_elem
    intro i
    apply finiteAdeleRingAway_eq_of_forall_eval_eq
    intro v
    rw [← basV_repr_map, ← basV_repr_map, h1 v]
  · apply Units.ext
    exact finiteAdeleRingAway_eq_of_forall_eval_eq h2

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedConjugatePlaceUniformiser
section
open IsDedekindDomain NumberField

namespace GlobalTheory.FixedPrime

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem le_of_under_le (P : Ideal (𝓞 E)) [hP : P.IsPrime]
    (h : ∀ x : 𝓞 E, IsCMField.ringOfIntegersComplexConj E x ∈ P → x ∈ P) (Q : Ideal (𝓞 E))
    (hQ : Q.under (𝓞 (maximalRealSubfield E)) ≤ P.under (𝓞 (maximalRealSubfield E))) : Q ≤ P := by
  intro y hy
  obtain ⟨s, hs⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E
    (y * IsCMField.ringOfIntegersComplexConj E y)).1 (by
      rw [map_mul, mul_comm]
      congr 1
      ext; simp)
  have h1 : s ∈ Q.under (𝓞 (maximalRealSubfield E)) := by
    rw [Ideal.under_def, Ideal.mem_comap, hs]
    exact Q.mul_mem_right _ hy
  have h2 := hQ h1
  rw [Ideal.under_def, Ideal.mem_comap, hs] at h2
  exact (hP.mem_or_mem h2).elim id (h y)

theorem isInertAt_under [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ x : 𝓞 E, IsCMField.ringOfIntegersComplexConj E x ∈ P.asIdeal → x ∈ P.asIdeal) :
    Formalism.UG.IsInertAt (maximalRealSubfield E) E (P.under (𝓞 (maximalRealSubfield E))) P := by
  classical
  haveI := P.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) P.asIdeal :=
    Algebra.unramified_iff_forall.1 inferInstance ⟨P.asIdeal, P.isPrime⟩
  set v := P.under (𝓞 (maximalRealSubfield E)) with hv
  have hva : v.asIdeal = P.asIdeal.under (𝓞 (maximalRealSubfield E)) := rfl
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  unfold Formalism.UG.IsInertAt
  rw [hva]
  have hle : (P.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ P.asIdeal := Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 (maximalRealSubfield E))) P.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 (maximalRealSubfield E))) P.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 (maximalRealSubfield E))
        (P.asIdeal.under (𝓞 (maximalRealSubfield E))) P.asIdeal).1 ‹_›).2
  have h2 : ¬ (P.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ P.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  set I := Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))
    (P.asIdeal.under (𝓞 (maximalRealSubfield E))) with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    exact v.ne_bot
  have hfac : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors I, p = P.asIdeal := by
    intro p hp
    obtain ⟨hpp, hpl⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hp
    have hp0 : p ≠ ⊥ := fun h0 => hI0 (le_bot_iff.1 (h0 ▸ hpl))
    refine (hpp.isMaximal hp0).eq_of_le P.isPrime.ne_top (le_of_under_le P.asIdeal h p ?_)
    exact (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hpp.ne_top)
      (Ideal.map_le_iff_le_comap.1 hpl)).ge
  obtain ⟨n, hn⟩ : ∃ n, I = P.asIdeal ^ n := by
    refine ⟨Multiset.card (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0]
    rw [Multiset.eq_replicate_card.2 hfac, Multiset.prod_replicate, Multiset.card_replicate]
  rcases n with _ | _ | n
  · exfalso
    rw [hn, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact P.isPrime.ne_top hle
  · simpa using hn
  · exact absurd (hn ▸ Ideal.pow_le_pow_right (by omega)) h2

theorem exists_isUnramInv [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E v P) :
    ∃ (σ : P.adicCompletion E →+* P.adicCompletion E) (ϖ : P.adicCompletion E),
      (∀ x : E, σ (algebraMap E (P.adicCompletion E) x) =
        algebraMap E (P.adicCompletion E) (IsCMField.complexConj E x)) ∧
      Formalism.UG.IsUnramInv ϖ σ (Ideal.absNorm v.asIdeal) := by
  obtain ⟨σ, ϖ, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.InertConj.exists_conj_completion E v P h
  refine ⟨σ, ϖ, h1, h2, h3, h5, h6, h4, ?_, ?_⟩
  · have a : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have b : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    omega
  · have hN : Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
      rw [← show Ideal.map _ v.asIdeal = P.asIdeal from h, Ideal.absNorm_algebraMap,
        ← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
      congr 1
      exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
        (𝓞 E) E).symm
    rw [← hN]
    exact Formalism.UG.P.tjcosets_card_residue P

end CM

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.FixedPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VStdOfOrthonormalSpan
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdFrame

theorem vStd_of_orthonormal_span : ∀ (D : D7) (i : Fin D.R.m), ((∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧ (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)) → VStd D i := by
  intro D i h
  refine vStd_of_frameChoice D i ⟨h.1, fun a => ?_⟩
  show (Vc D i).frame a ∈ (Vc D i).L0
  rw [h.2]
  exact Submodule.subset_span ⟨a, rfl⟩

end GlobalTheory.StdFrame
end

