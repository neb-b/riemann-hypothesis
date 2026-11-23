module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LPosExtE
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGoodEvA
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

variable {D : D7}

theorem repr_map' {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem ae_ext (z z' : AE D) (hi : ∀ w, compInf D.host.F D.host.E w z = compInf D.host.F D.host.E w z')
    (hf : ∀ v, cv D v z = cv D v z') : z = z' := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  apply (Algebra.TensorProduct.basis (AF D.host.F) b).repr.injective
  refine Finsupp.ext fun k => Prod.ext ?_ ?_
  · funext w
    have h1 := repr_map' (evInf D.host.F w) b z k
    have h2 := repr_map' (evInf D.host.F w) b z' k
    have h : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z' := hi w
    rw [h, h2] at h1
    exact h1.symm
  · refine FiniteAdeleRing.ext _ fun v => ?_
    have h1 := repr_map' (evFin D.host.F v) b z k
    have h2 := repr_map' (evFin D.host.F v) b z' k
    have h : Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z' := hf v
    rw [h, h2] at h1
    exact h1.symm


open Classical in
def indS (S : Finset (Pl D)) : Af D.host.F :=
  ⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [if_pos h]; exact one_mem (v.adicCompletionIntegers D.host.F)
    · simp only [if_neg h]; exact zero_mem (v.adicCompletionIntegers D.host.F)⟩

open Classical in
theorem indS_apply (S : Finset (Pl D)) (v : Pl D) : (indS S) v = if v ∈ S then 1 else 0 := rfl

def eS (S : Finset (Pl D)) : AE D := ((1, indS S) : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem isIdem_eS (S : Finset (Pl D)) : IsIdem S (eS S) := by
  classical
  refine ⟨fun w => ?_, fun v => ?_⟩
  · change (evInf D.host.F w (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [show evInf D.host.F w (1, indS S) = 1 from rfl]
    rfl
  · change (evFin D.host.F v (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = _
    rw [show evFin D.host.F v (1, indS S) = if v ∈ S then 1 else 0 from rfl]
    split_ifs
    · rfl
    · exact TensorProduct.zero_tmul _ _

theorem infPart_eS (S : Finset (Pl D)) : infPart D (eS S) = 1 := by
  simp only [infPart, eS, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rfl

theorem finPart_eS (S : Finset (Pl D)) :
    finPart D (eS S) = algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (indS S) := by
  simp only [finPart, eS, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem cv_eq (v : Pl D) (z : AE D) :
    cv D v z = Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _), map_add (f := _)]
  | tmul a x => rfl

end PositivityTheory.Rg.Rsw.L.LGoodEv

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LIdemEx
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LIdemEx

variable {D : D7}

theorem repr_map' {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem ae_ext (z z' : AE D) (hi : ∀ w, compInf D.host.F D.host.E w z = compInf D.host.F D.host.E w z')
    (hf : ∀ v, cv D v z = cv D v z') : z = z' := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  apply (Algebra.TensorProduct.basis (AF D.host.F) b).repr.injective
  refine Finsupp.ext fun k => Prod.ext ?_ ?_
  · funext w
    have h1 := repr_map' (evInf D.host.F w) b z k
    have h2 := repr_map' (evInf D.host.F w) b z' k
    have h : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z' := hi w
    rw [h, h2] at h1
    exact h1.symm
  · refine FiniteAdeleRing.ext _ fun v => ?_
    have h1 := repr_map' (evFin D.host.F v) b z k
    have h2 := repr_map' (evFin D.host.F v) b z' k
    have h : Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z' := hf v
    rw [h, h2] at h1
    exact h1.symm


open Classical in
def indS (S : Finset (Pl D)) : Af D.host.F :=
  ⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [if_pos h]; exact one_mem (v.adicCompletionIntegers D.host.F)
    · simp only [if_neg h]; exact zero_mem (v.adicCompletionIntegers D.host.F)⟩

def eS (S : Finset (Pl D)) : AE D := ((1, indS S) : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem isIdem_eS (S : Finset (Pl D)) : IsIdem S (eS S) := by
  classical
  refine ⟨fun w => ?_, fun v => ?_⟩
  · change (evInf D.host.F w (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [show evInf D.host.F w (1, indS S) = 1 from rfl]
    rfl
  · change (evFin D.host.F v (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = _
    rw [show evFin D.host.F v (1, indS S) = if v ∈ S then 1 else 0 from rfl]
    split_ifs
    · rfl
    · exact TensorProduct.zero_tmul _ _

theorem compInf_cA (w : InfinitePlace D.host.F) (z : AE D) :
    compInf D.host.F D.host.E w (cA D z) =
      (Algebra.TensorProduct.map (AlgHom.id D.host.F w.Completion) D.sp.cm.sig).toRingHom (compInf D.host.F D.host.E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _)]
  | tmul a x => rfl

theorem cv_cA (v : Pl D) (z : AE D) :
    cv D v (cA D z) =
      (Algebra.TensorProduct.map (AlgHom.id D.host.F (Fv D.host.F v)) D.sp.cm.sig).toRingHom (cv D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _)]
  | tmul a x => rfl

theorem idem_props (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) : e * e = e ∧ cA D e = e := by
  classical
  refine ⟨ae_ext _ _ (fun w => ?_) (fun v => ?_), ae_ext _ _ (fun w => ?_) (fun v => ?_)⟩
  · rw [map_mul, he.1 w, one_mul]
  · rw [map_mul, he.2 v]
    split_ifs <;> simp
  · rw [compInf_cA, he.1 w, RingHom.map_one]
  · rw [cv_cA, he.2 v]
    split_ifs <;> simp

end PositivityTheory.Rg.Rsw.L.LIdemEx

namespace PositivityTheory.Rg.Rsw.L

theorem idemEx : IdemEx := fun _ S =>
  ⟨⟨_, LIdemEx.isIdem_eS S⟩, fun e he => LIdemEx.idem_props S e he⟩

end PositivityTheory.Rg.Rsw.L

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajorB
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem repr_map {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem infPart_eq_of {e e' : AE D}
    (h : ∀ w, compInf D.host.F D.host.E w e = compInf D.host.F D.host.E w e') : infPart D e = infPart D e' := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) e =
    Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) e'
  apply (Algebra.TensorProduct.basis (Ainf D.host.F) b).repr.injective
  refine Finsupp.ext fun k => ?_
  rw [repr_map, repr_map]
  funext w
  have h1 := repr_map (evInf D.host.F w) b e k
  have h2 := repr_map (evInf D.host.F w) b e' k
  have hw : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) e =
      Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) e' := h w
  rw [hw, h2] at h1
  exact h1.symm

theorem infPart_idem {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) : infPart D e = 1 :=
  (infPart_eq_of (e' := 1) fun w => (he.1 w).trans (map_one _).symm).trans (map_one _)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem cv_eq (v : Pl D) (a : AE D) :
    cv D v a = Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
      (finPart D a) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _), map_add (f := _)]
  | tmul x y =>
    show Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) (x ⊗ₜ[D.host.F] y) =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (x ⊗ₜ[D.host.F] y))
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rfl

theorem cv_congr (v : Pl D) {a a' : AE D} (h : finPart D a = finPart D a') : cv D v a = cv D v a' := by
  rw [cv_eq, cv_eq, h]

def afF (D : D7) : AF D.host.F := (0, 1)

theorem fstA_afF : fstA D.host.F (afF D) = 0 := rfl

theorem sndA_afF : sndA D.host.F (afF D) = 1 := rfl

def sF (D : D7) : AE D := afF D ⊗ₜ[D.host.F] (1 : D.host.E)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem infPart_sF : infPart D (sF D) = 0 := by
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    (afF D ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Algebra.TensorProduct.map_tmul, fstA_afF, TensorProduct.zero_tmul]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem finPart_sF : finPart D (sF D) = 1 := by
  show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
    (afF D ⊗ₜ[D.host.F] (1 : D.host.E)) = 1
  rw [Algebra.TensorProduct.map_tmul, sndA_afF]
  rfl

theorem compAt_smul (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (c : AE D) (x : Mx D m n) :
    compAt θ τ (c • x) = θ τ (infPart D c) • compAt θ τ x := by
  ext i j
  simp [compAt, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajorC
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7}

theorem prodSB {X : Type} [TopologicalSpace X] {a b : ℕ} (G : Fin a → (Fin 1 → Fin b → X) → ℂ)
    (hG : ∀ i, G i ∈ GlobalTheory.WeilM.SB (Fin 1 → Fin b → X)) :
    (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) ∈ GlobalTheory.WeilM.SB (Fin a → Fin b → X) := by
  have hG' : ∀ i, IsLocallyConstant (G i) ∧ HasCompactSupport (G i) := hG
  have hrow : ∀ i : Fin a, Continuous fun z : Fin a → Fin b → X => (fun (_ : Fin 1) j => z i j) :=
    fun i => continuous_pi fun _ => continuous_pi fun j => (continuous_apply j).comp (continuous_apply i)
  show IsLocallyConstant (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) ∧
    HasCompactSupport (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j))
  refine ⟨?_, ?_⟩
  · have hfun : (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) =
        ∏ i, (fun z : Fin a → Fin b → X => G i (fun _ j => z i j)) := by
      funext z
      rw [Finset.prod_apply]
    rw [hfun]
    exact Finset.prod_induction _ IsLocallyConstant (fun f g hf hg => hf.comp₂ hg (· * ·))
      (IsLocallyConstant.const 1) (fun i _ => (hG' i).1.comp_continuous (hrow i))
  · let S : Set (Fin a → Fin b → X) := ⋂ i, (fun z : Fin a → Fin b → X => (fun (_ : Fin 1) j => z i j)) ⁻¹' tsupport (G i)
    let gm : (Fin a → Fin 1 → Fin b → X) → (Fin a → Fin b → X) := fun w i j => w i 0 j
    have hgm : Continuous gm :=
      continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply j).comp ((continuous_apply 0).comp (continuous_apply i))
    have hK : IsCompact (gm '' Set.univ.pi fun i => tsupport (G i)) :=
      (isCompact_univ_pi fun i => (hG' i).2).image hgm
    have hSc : IsClosed S := isClosed_iInter fun i => (isClosed_tsupport (G i)).preimage (hrow i)
    have hsub : tsupport (fun z : Fin a → Fin b → X => ∏ i, G i (fun _ j => z i j)) ⊆ S := by
      refine closure_minimal ?_ hSc
      intro z hz
      have hz' : ∏ i, G i (fun _ j => z i j) ≠ 0 := hz
      rw [Finset.prod_ne_zero_iff] at hz'
      exact Set.mem_iInter.2 fun i => subset_tsupport _ (hz' i (Finset.mem_univ i))
    have hSK : S ⊆ gm '' Set.univ.pi fun i => tsupport (G i) := by
      intro z hz
      refine ⟨fun i _ j => z i j, fun i _ => Set.mem_iInter.1 hz i, rfl⟩
    exact hK.of_isClosed_subset (isClosed_tsupport _) (hsub.trans hSK)

theorem rowSB (θ : InfFam D) {m n : ℕ} (s : AE D) (hs : infPart D s = 0) (hs' : finPart D s = 1)
    (h : Mx D m n → ℂ) (hh : h ∈ schwartzA θ m n) :
    ∃ G ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E),
      ∀ y : Mx D m n, h (s • y) = G (fun i j => finPart D (y i j)) := by
  change h ∈ Submodule.span ℂ _ at hh
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    refine ⟨f (fun _ _ _ => 0) • g, Submodule.smul_mem _ _ hg, fun y => ?_⟩
    have h1 : (fun τ i j => Formalism.IndefR.Datum.compAt θ τ (s • y) i j) = fun _ _ _ => (0 : ℂ) := by
      funext τ i j
      have hc : Formalism.IndefR.Datum.compAt θ τ (s • y) i j = θ τ (Formalism.L2.Theta.infPart D (s * y i j)) := rfl
      rw [hc, map_mul, hs, zero_mul, map_zero]
    have h2 : (fun i j => Formalism.L2.Theta.finPart D ((s • y) i j)) = fun i j => Formalism.L2.Theta.finPart D (y i j) := by
      funext i j
      have hc : Formalism.L2.Theta.finPart D ((s • y) i j) = Formalism.L2.Theta.finPart D (s * y i j) := rfl
      rw [hc, map_mul, hs', one_mul]
    show f (fun τ i j => Formalism.IndefR.Datum.compAt θ τ (s • y) i j) *
        g (fun i j => Formalism.L2.Theta.finPart D ((s • y) i j)) = _
    rw [h1, h2, Pi.smul_apply, smul_eq_mul]
  | zero => exact ⟨0, Submodule.zero_mem _, fun y => rfl⟩
  | add x z _ _ hx hz =>
    obtain ⟨G1, hG1, e1⟩ := hx
    obtain ⟨G2, hG2, e2⟩ := hz
    exact ⟨G1 + G2, Submodule.add_mem _ hG1 hG2, fun y => by rw [Pi.add_apply, Pi.add_apply, e1, e2]⟩
  | smul c x _ hx =>
    obtain ⟨G1, hG1, e1⟩ := hx
    exact ⟨c • G1, Submodule.smul_mem _ _ hG1, fun y => by rw [Pi.smul_apply, Pi.smul_apply, e1]⟩

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LPosExt
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

theorem posExt : PosExt := by
  intro X _ _ _ _ _ _ A hc hmul hstar hsep hone
  exact ⟨fun L hL => LPosExt.exist A hc hstar hone L hL, LPosExt.uniq' A hc hmul hstar hsep hone⟩

end PositivityTheory.Rg.Rsw.L

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LWMajD
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LWMaj

variable {D : D7}

theorem unifLevel {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (C : Set (GA D S)) (hC : IsCompact C) :
    ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ g ∈ C, om (g, 1) f ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
  obtain ⟨U, hUo, hU⟩ := hf.level

  let a : GA D S → WO S T →+ WO S T := fun g =>
    { toFun := fun u => actO S T g⁻¹ 1 u
      map_zero' := by simp [actO]
      map_add' := fun u v => by simp [actO, Matrix.mul_add, Matrix.add_mul] }
  let U' : AddSubgroup (WO S T) := ⨅ g ∈ C, U.comap (a g)
  have hcont : Continuous fun p : GA D S × WO S T => actO S T p.1⁻¹ 1 p.2 := by
    simp only [actO, inv_inv]
    exact (continuous_const.matrix_mul continuous_snd).matrix_mul ((GlobalTheory.MixModel.continuous_mt S).comp continuous_fst)
  have hmem : ∀ u, u ∈ U' ↔ ∀ g ∈ C, actO S T g⁻¹ 1 u ∈ U := fun u => by
    rw [AddSubgroup.mem_iInf]
    exact forall_congr' fun g => by rw [AddSubgroup.mem_iInf]; rfl
  have hopen : IsOpen (U' : Set (WO S T)) := by
    have hn : C ×ˢ ({0} : Set (WO S T)) ⊆ (fun p : GA D S × WO S T => actO S T p.1⁻¹ 1 p.2) ⁻¹' U := by
      rintro ⟨g, u⟩ ⟨-, hu⟩
      simp only [Set.mem_singleton_iff] at hu
      subst hu
      simp [actO, U.zero_mem]
    obtain ⟨s, v, -, hv, hCs, h0v, hsv⟩ :=
      generalized_tube_lemma hC isCompact_singleton (hUo.preimage hcont) hn
    refine AddSubgroup.isOpen_of_mem_nhds U' (g := 0) ?_
    refine Filter.mem_of_superset (hv.mem_nhds (h0v rfl)) fun u hu => ?_
    refine (hmem u).2 fun g hg => ?_
    have h := hsv (Set.mk_mem_prod (hCs hg) hu)
    rw [Set.mem_preimage] at h
    exact h
  refine ⟨U', hopen, fun g hg => ⟨hom.om_pres _ _ hf, fun u hu h0 => ?_⟩⟩
  have hu' : actO S T g⁻¹ 1 u ∈ U := by
    exact (hmem u).1 hu g hg
  have h0' : (actO S T g⁻¹ 1 u).map (infPart D) = 0 := by
    simp only [actO, Matrix.map_mul, h0, Matrix.zero_mul, Matrix.mul_zero]
  have h1 := hom.om_heis g 1 (actO S T g⁻¹ 1 u) f hf
  rw [hU _ hu' h0'] at h1
  have h2 : actO S T g 1 (actO S T g⁻¹ 1 u) = u := by
    simp only [actO, inv_inv, GlobalTheory.MixModel.mt_one, Matrix.one_mul, Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul_inv,
      Matrix.mul_one]
  rw [h2] at h1
  exact h1.symm

end PositivityTheory.Rg.Rsw.L.LWMaj

end
end

