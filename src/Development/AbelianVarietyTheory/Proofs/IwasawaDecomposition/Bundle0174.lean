module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitFrames
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinPartAlgebraMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LocWeil
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocWeil.PlaceIdem

section General

variable (F : Type) [Field F] [NumberField F]

theorem evalV_single_same (v : HeightOneSpectrum (𝓞 F)) : evalV F v (singleV F v 1) = 1 :=
  RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v 1

theorem evalV_single_ne {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) : evalV F u (singleV F v 1) = 0 :=
  RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) 1 h

theorem af_ext {a b : Af F} (h : ∀ u, evalV F u a = evalV F u b) : a = b :=
  DFunLike.ext _ _ h

def eFin (v : HeightOneSpectrum (𝓞 F)) : AF F := pairA F 0 (singleV F v 1)

def eInf (v : InfinitePlace F) : AF F := pairA F (Pi.single v 1) 0

theorem eFin_mul_eFin {u v : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) : eFin F u * eFin F v = 0 := by
  refine Prod.ext (mul_zero _) ?_
  change singleV F u 1 * singleV F v 1 = 0
  refine af_ext F fun w => ?_
  rw [map_mul, map_zero]
  by_cases hw : w = u
  · subst hw
    rw [evalV_single_ne F h, mul_zero]
  · rw [evalV_single_ne F hw, zero_mul]

theorem eFin_mul_eInf (u : HeightOneSpectrum (𝓞 F)) (v : InfinitePlace F) : eFin F u * eInf F v = 0 :=
  Prod.ext (zero_mul _) (mul_zero _)

theorem eInf_mul_eInf {u v : InfinitePlace F} (h : u ≠ v) : eInf F u * eInf F v = 0 := by
  refine Prod.ext ?_ (mul_zero _)
  funext w
  change (Pi.single u 1 : ∀ w : InfinitePlace F, w.Completion) w *
    (Pi.single v 1 : ∀ w : InfinitePlace F, w.Completion) w = 0
  by_cases hw : w = u
  · subst hw
    rw [Pi.single_eq_of_ne h, mul_zero]
  · rw [Pi.single_eq_of_ne hw, zero_mul]

theorem eq_zero_of_idem (a : AF F) (h1 : ∀ v, eFin F v * a = 0) (h2 : ∀ v, eInf F v * a = 0) : a = 0 := by
  refine Prod.ext ?_ ?_
  · funext w
    have h : (Pi.single w 1 : ∀ w : InfinitePlace F, w.Completion) w * a.1 w = 0 :=
      congrFun (congrArg Prod.fst (h2 w)) w
    rw [Pi.single_eq_same, one_mul] at h
    exact h
  · refine af_ext F fun w => ?_
    have h : singleV F w 1 * sndA F a = 0 := congrArg Prod.snd (h1 w)
    have h' := congrArg (evalV F w) h
    rw [map_mul, evalV_single_same, one_mul] at h'
    exact h'

theorem tensor_eq_zero {K E R I : Type} [Field K] [Field E] [Algebra K E] [CommRing R] [Algebra K R] (e : I → R)
    (he : ∀ a : R, (∀ i, e i * a = 0) → a = 0) (x : R ⊗[K] E)
    (hx : ∀ i, algebraMap R (R ⊗[K] E) (e i) * x = 0) : x = 0 := by
  let b := Algebra.TensorProduct.basis R (Module.Free.chooseBasis K E)
  refine b.ext_elem fun j => ?_
  rw [map_zero]
  refine he _ fun i => ?_
  have h := hx i
  rw [← Algebra.smul_def] at h
  have h' := congrArg (fun y => b.repr y j) h
  simpa using h'

theorem sum_single_one : (∑ v : InfinitePlace F, fstA F (eInf F v)) = 1 := by
  change (∑ v : InfinitePlace F, (Pi.single v 1 : ∀ w : InfinitePlace F, w.Completion)) = fun _ => 1
  exact Finset.univ_sum_single (fun w : InfinitePlace F => (1 : w.Completion))

theorem ext_eInf (σ : F →+* ℂ) (v : InfinitePlace F) :
    GlobalTheory.InfAdeleCM.ext σ (fstA F (eInf F v)) = if InfinitePlace.mk σ = v then 1 else 0 := by
  rw [GlobalTheory.InfAdeleCM.ext_apply]
  change InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ)
    ((Pi.single v 1 : ∀ w : InfinitePlace F, w.Completion) (InfinitePlace.mk σ)) = _
  split_ifs with h
  · subst h
    rw [Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, map_zero]

end General

def plc (D : D7) (τ : D.what₂.Tau) : InfinitePlace D.host.F :=
  InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))

theorem plc_bijective (D : D7) : Function.Bijective (plc D) := GlobalTheory.CMTypePlaces.places_bijective D

theorem idem_inl (D : D7) (v : FinF D) :
    idem D (.inl v) = algebraMap (AF D.host.F) (AE D) (eFin D.host.F v) := rfl

theorem idem_inr (D : D7) (τ : D.what₂.Tau) :
    idem D (.inr τ) = algebraMap (AF D.host.F) (AE D) (eInf D.host.F (plc D τ)) := rfl

theorem infPart_algebraMap (D : D7) (a : AF D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) a) = fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

theorem finPart_algebraMap (D : D7) (a : AF D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) a) = sndA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

theorem idem_props : ∀ D : D7, (∀ v v' : Pl D, v ≠ v' → idem D v * idem D v' = 0) ∧ (∀ θ : InfF D, IsInfFam θ → ∀ τ τ', θ τ' (infPart D (idem D (.inr τ))) = if τ' = τ then 1 else 0) ∧ (∀ τ, finPart D (idem D (.inr τ)) = 0) ∧ infPart D (∑ τ, idem D (.inr τ)) = 1 ∧ (∀ v : FinF D, ∃ a, IsPlaceIdem D v a ∧ idem D (.inl v) = algebraMap (AF D.host.F) (AE D) a) ∧ ∀ x : AE D, (∀ v, idem D v * x = 0) → x = 0 := by
  intro D
  have hb := plc_bijective D
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (v | τ) (v' | τ') h
    · rw [idem_inl, idem_inl, ← RingHom.map_mul, eFin_mul_eFin _ fun e => h (congrArg _ e), RingHom.map_zero]
    · rw [idem_inl, idem_inr, ← RingHom.map_mul, eFin_mul_eInf, RingHom.map_zero]
    · rw [idem_inr, idem_inl, ← RingHom.map_mul, mul_comm, eFin_mul_eInf, RingHom.map_zero]
    · rw [idem_inr, idem_inr, ← RingHom.map_mul, eInf_mul_eInf _ fun e => h (congrArg _ (hb.1 e)), RingHom.map_zero]
  · intro θ hθ τ τ'
    haveI := D.sp.cm.totReal
    have h := GlobalTheory.InfAdeleCM.hom_tmul (tauE D τ') (θ τ') (hθ τ').1 (hθ τ').2
      (fstA D.host.F (eInf D.host.F (plc D τ))) 1
    rw [RingHom.map_one, mul_one, ext_eInf] at h
    rw [idem_inr, infPart_algebraMap]
    refine h.trans ?_
    exact if_congr (hb.1.eq_iff (a := τ') (b := τ)) rfl rfl
  · intro τ
    rw [idem_inr, finPart_algebraMap]
    exact TensorProduct.zero_tmul _ _
  · have h : (∑ τ, idem D (.inr τ)) =
        algebraMap (AF D.host.F) (AE D) (∑ v : InfinitePlace D.host.F, eInf D.host.F v) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hb.sum_comp, map_sum (algebraMap (AF D.host.F) (AE D))]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h, infPart_algebraMap, map_sum (fstA D.host.F), sum_single_one]
    rfl
  · intro v
    exact ⟨eFin D.host.F v, ⟨singleV D.host.F v 1, rfl, evalV_single_same _ v, fun v' h => evalV_single_ne _ h⟩, rfl⟩
  · intro x hx
    refine tensor_eq_zero (Sum.elim (eFin D.host.F) fun τ => eInf D.host.F (plc D τ)) (fun a ha => ?_) x ?_
    · refine eq_zero_of_idem _ a (fun v => ha (.inl v)) fun w => ?_
      obtain ⟨τ, rfl⟩ := hb.2 w
      exact ha (.inr τ)
    · rintro (v | τ)
      · exact hx (.inl v)
      · exact hx (.inr τ)

end GlobalTheory.LocWeil.PlaceIdem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevel
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.DefiniteClassFinite

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

noncomputable abbrev sig : L →ₐ[maximalRealSubfield L] L :=
  ((IsCMField.complexConj L : L ≃ₐ[maximalRealSubfield L] L) : L →ₐ[maximalRealSubfield L] L)

noncomputable def swapAd : ReciprocityTheory.Aut.AL L ≃ₐ[maximalRealSubfield L]
    TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L :=
  Algebra.TensorProduct.comm _ _ _

theorem flip_symm_tmul (a : L) (b : Af (maximalRealSubfield L)) : (swapAd L).symm (b ⊗ₜ a) = a ⊗ₜ b := rfl

theorem flip_conj (x : ReciprocityTheory.Aut.AL L) :
    swapAd L (ReciprocityTheory.Aut.conjAL L x) = sigR (Af (maximalRealSubfield L)) (sig L) (swapAd L x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

noncomputable def flipGL (n : ℕ) : GL (Fin n) (ReciprocityTheory.Aut.AL L) ≃*
    GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) :=
  Units.mapEquiv (swapAd L).toRingEquiv.mapMatrix.toMulEquiv

theorem JR_one (n : ℕ) : JR (F := ↥(maximalRealSubfield L)) (Af (maximalRealSubfield L)) (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  unfold JR
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem mem_GA_iff {n : ℕ} (g : GL (Fin n) (ReciprocityTheory.Aut.AL L)) :
    g ∈ ReciprocityTheory.Aut.GA L n ↔
      flipGL L n g ∈ HR (Af (maximalRealSubfield L)) (sig L) (1 : Matrix (Fin n) (Fin n) L) := by
  set M : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) := (g : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L))
  have hc : Formalism.UG.cT (sigR (Af (maximalRealSubfield L)) (sig L)) (M.map (swapAd L)) =
      (ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M).map (swapAd L) := by
    ext i j; simp [Formalism.UG.cT, ReciprocityTheory.Aut.conjT, flip_conj]
  change M * ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M = 1 ↔
    Formalism.UG.cT (sigR (Af (maximalRealSubfield L)) (sig L)) (M.map (swapAd L)) *
      JR (F := ↥(maximalRealSubfield L)) (Af (maximalRealSubfield L)) (1 : Matrix (Fin n) (Fin n) L) * M.map (swapAd L) =
      JR (F := ↥(maximalRealSubfield L)) (Af (maximalRealSubfield L)) (1 : Matrix (Fin n) (Fin n) L)
  rw [hc, JR_one, mul_one]
  have key : ∀ X Y : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L),
      X.map (swapAd L) * Y.map (swapAd L) = (X * Y).map (swapAd L) := fun X Y =>
    (map_mul (swapAd L).toRingEquiv.mapMatrix X Y).symm
  rw [key, mul_eq_one_comm]
  constructor
  · intro h; rw [h]; exact Matrix.map_one _ (map_zero _) (map_one _)
  · intro h
    apply (swapAd L).toRingEquiv.mapMatrix.injective
    rw [map_one]; exact h

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

abbrev Jn (n : ℕ) : Matrix (Fin n) (Fin n) L := 1

abbrev Hf (n : ℕ) := HA (Af (maximalRealSubfield L)) (sig L) (Jn L n)

noncomputable def back (n : ℕ) : Hf L n →* Formalism.AUTREP.GAf L n where
  toFun h := ⟨(flipGL L n).symm (HA.mat _ _ _ h), by
    rw [mem_GA_iff, MulEquiv.apply_symm_apply]; exact h.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (flipGL L n).symm
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (flipGL L n).symm (HA.mat _ _ _ x) (HA.mat _ _ _ y)

noncomputable def fwd (n : ℕ) (g : Formalism.AUTREP.GAf L n) : Hf L n :=
  ⟨flipGL L n g.1, (mem_GA_iff L g.1).1 g.2⟩

theorem back_fwd (n : ℕ) (g : Formalism.AUTREP.GAf L n) : back L n (fwd L n g) = g := by
  apply Subtype.ext
  exact MulEquiv.symm_apply_apply (flipGL L n) g.1

theorem back_smul (n : ℕ) (γ : HFinIn (Af (maximalRealSubfield L)) (sig L) (Jn L n)) (h : Hf L n) :
    back L n (γ • h) = back L n γ.1 * back L n h := by
  apply Subtype.ext
  exact map_mul (flipGL L n).symm (γ.1.1) (HA.mat _ _ _ h)

theorem back_mem_GQ (n : ℕ) (γ : HFinIn (Af (maximalRealSubfield L)) (sig L) (Jn L n)) :
    back L n γ.1 ∈ ReciprocityTheory.Aut.GQ L n := by
  obtain ⟨γ0, hγ0, e⟩ := γ.2
  rw [ReciprocityTheory.Aut.GQ, Subgroup.mem_subgroupOf]
  refine ⟨γ0, ?_, ?_⟩
  · change (γ0 : Matrix (Fin n) (Fin n) L) * ReciprocityTheory.Aut.conjT _ (γ0 : Matrix (Fin n) (Fin n) L) = 1
    have h0 : Formalism.UG.cT (sig L : L →+* L) (γ0 : Matrix (Fin n) (Fin n) L) * 1 * (γ0 : Matrix (Fin n) (Fin n) L) = 1 := hγ0
    rw [mul_one] at h0
    rw [mul_eq_one_comm]
    exact h0
  · apply Units.ext
    have e' : Units.val (γ.1.1 : GL (Fin n) _) =
        Units.val (Formalism.UG.bc (inclR (F := ↥(maximalRealSubfield L)) (E := L) (Af (maximalRealSubfield L))) γ0) := by
      rw [e]; rfl
    change ((γ0 : Matrix (Fin n) (Fin n) L)).map Algebra.TensorProduct.includeLeftRingHom =
      ((γ.1.1 : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map (swapAd L).symm
    rw [e']
    ext i j
    rfl

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

noncomputable def intSet : Set (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) :=
  (swapAd L).symm ⁻¹' (ReciprocityTheory.Aut.ALint L : Set (ReciprocityTheory.Aut.AL L))

theorem isOpen_intSet : IsOpen (intSet L) := by
  classical
  let b0 := Module.finBasisOfFinrankEq (maximalRealSubfield L) L
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := L) (Finset.univ.image b0)
  let b := b0.unitsSMul (fun _ => Units.mk0 ((y : maximalRealSubfield L)) (by exact_mod_cast hy0))
  have hb : ∀ i, IsIntegral ℤ (b i) := by
    intro i
    rw [Module.Basis.unitsSMul_apply]
    have := hy _ (Finset.mem_image_of_mem b0 (Finset.mem_univ i))
    simpa [Units.smul_def, Int.cast_smul_eq_zsmul] using this
  let B := Algebra.TensorProduct.basis (Af (maximalRealSubfield L)) b
  haveI : IsModuleTopology (Af (maximalRealSubfield L))
      (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) := ⟨rfl⟩
  have hc : Continuous B.equivFun := IsModuleTopology.continuous_of_linearMap B.equivFun.toLinearMap
  let H : AddSubgroup (Fin 2 → Af (maximalRealSubfield L)) :=
    (ReciprocityTheory.Aut.ALint L).toAddSubgroup.comap
      ((swapAd L).symm.toRingEquiv.toAddMonoidHom.comp B.equivFun.symm.toLinearMap.toAddMonoidHom)
  have hW := GlobalTheory.AdLat.OpenLat.isOpen_integral (maximalRealSubfield L)
  have hV : (Set.univ.pi fun _ : Fin 2 => {a : Af (maximalRealSubfield L) |
      ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers (maximalRealSubfield L) v}) ⊆ H := by
    intro c hc'
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq] at hc'
    change (swapAd L).symm (B.equivFun.symm c) ∈ ReciprocityTheory.Aut.ALint L
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Module.Basis.equivFun_symm_apply, map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, flip_symm_tmul]
    have : b i ⊗ₜ[maximalRealSubfield L] c i =
        (b i ⊗ₜ[maximalRealSubfield L] (1 : Af (maximalRealSubfield L))) * (1 ⊗ₜ c i) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [this]
    exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨b i, hb i⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨c i, hc' i, rfl⟩))
  have hHo : IsOpen (H : Set (Fin 2 → Af (maximalRealSubfield L))) := by
    apply AddSubgroup.isOpen_of_mem_nhds H (g := 0)
    apply Filter.mem_of_superset _ hV
    apply (isOpen_set_pi Set.finite_univ fun _ _ => hW).mem_nhds
    intro i _ v
    exact (v.adicCompletionIntegers (maximalRealSubfield L)).zero_mem
  have : intSet L = B.equivFun ⁻¹' H := by
    ext x
    simp [intSet, H]
  rw [this]
  exact hHo.preimage hc

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

noncomputable def Kmax (n : ℕ) : Subgroup (Hf L n) := (ReciprocityTheory.Aut.Umax L n).comap (back L n)

theorem isOpen_Kmax (n : ℕ) : IsOpen (Kmax L n : Set (Hf L n)) := by
  refine ⟨{x : GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) |
    ∀ i j, (x : Matrix (Fin n) (Fin n) _) i j ∈ intSet L}, ?_, ?_⟩
  · have : {x : GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) |
        ∀ i j, (x : Matrix (Fin n) (Fin n) _) i j ∈ intSet L} =
        ⋂ i, ⋂ j, (fun x : GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) =>
          (x : Matrix (Fin n) (Fin n) _) i j) ⁻¹' intSet L := by
      ext x; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_intSet L).preimage ((Units.continuous_val (M := Matrix (Fin n) (Fin n)
        (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L))).matrix_elem i j)
  · ext h
    rfl

theorem herm_one (n : ℕ) : IsHermND (sig L) (Jn L n) := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h, Ne.symm h]

theorem exists_finset_double_cosets_Umax (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) :
    ∃ T : Finset (Formalism.AUTREP.GAf L n), ∀ g : Formalism.AUTREP.GAf L n,
      ∃ (γ : ReciprocityTheory.Aut.GQ L n) (t : Formalism.AUTREP.GAf L n) (u : Formalism.AUTREP.GAf L n),
        t ∈ T ∧ u ∈ ReciprocityTheory.Aut.Umax L n ∧ g = (γ : Formalism.AUTREP.GAf L n) * t * u := by
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.Mem.ClassFinite.exists_finset_classes _ L (sig L)
    (GlobalTheory.AdelicU.isCMExt_of_isCMField L) n (Jn L n) (herm_one L n) (Kmax L n) (isOpen_Kmax L n)
  refine ⟨S.image (back L n), fun g => ?_⟩
  obtain ⟨γ, s, hs, k, hk, e⟩ := hS (fwd L n g)
  refine ⟨⟨back L n γ.1, back_mem_GQ L n γ⟩, back L n s, back L n k,
    Finset.mem_image_of_mem _ hs, hk, ?_⟩
  have := congrArg (back L n) e
  rw [back_fwd, back_smul, map_mul, ← mul_assoc] at this
  exact this

end GlobalTheory.DefiniteClassFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianVectorAnnihilatorEquationsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianVector_annihilator_equations : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (v : F.H), HasCoeff F v (expPS (gaussPoly A x)) → (∀ (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inl i) * f)) v = x (Sum.inl i) * inner ℂ (F.ι f) v + ∑ j, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inr j) f)) v) ∧ (∀ (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inr j) * f)) v = x (Sum.inr j) * inner ℂ (F.ι f) v + ∑ i, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) f)) v) := by
  first | exact @GlobalTheory.OscGauss.gauss_annihilator | exact GlobalTheory.OscGauss.gauss_annihilator | (intros; apply GlobalTheory.OscGauss.gauss_annihilator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ICCptEq
section
noncomputable section

namespace GlobalTheory.Mem.SJ.RowB

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem iC_cpt_eq {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin ((lv (fc X.zs) b).dQ t) → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [CxData.iC, lin, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ, cpt, RingHom.id_apply]

theorem theta_eq : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.IotaRd cr → ∀ y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL, X.Θ Bs.μ0 (X.jR Bs.μ0 (eV Bs.μ0 y)) = M.eR (D.what₂.iota D.what₂.mu0 (M.cF (cpt D.what₂.embLL y))) := by
  intro D Bs A X fc s R cr M eV hF hI y
  rw [M.cF_eq, hI y, M.eR_eq, X.rowMat_base cr true hF.h2, Matrix.one_mulVec, iC_cpt_eq, hF.theta y]
  rfl

end GlobalTheory.Mem.SJ.RowB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerTwOfSmul
section
noncomputable section

namespace GlobalTheory.Mem.SJ.Pair

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Bs : DefBase D.what₂.LL} {A : DefAmb Bs} {X : CxData A} {fc : DefSub A → DefFace Bs} {s : Bool}
  {R : Read D X fc s} {cr : Crd A fc}

theorem cpt_single {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} (i : Fin n) :
    (fun k => σ ((Pi.single i 1 : Fin n → K) k)) = (Pi.single i 1 : Fin n → ℂ) := by
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem sum_coord_jN (M : Seam R cr) (u : D.what₂.Word) (φ : D.what₂.Mu u) :
    ∑ i, M.cφ u φ i • D.jN u (R.eNu u (Pi.single i 1)) = φ := by
  have h : ∀ i, D.jN u (R.eNu u (Pi.single i 1)) = (M.cφ u).symm (Pi.single i 1) := fun i => by
    rw [← M.cφ_eq]
    exact congrArg _ (cpt_single D.what₂.embLL i)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h, ← map_smul, ← map_sum]
  rw [LinearEquiv.symm_apply_eq]
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem sum_coord_eMu (M : Seam R cr) (u : D.what₂.Word) (φ : D.what₂.Mu u) :
    ∑ i, M.cφ u φ i • D.eMu u (D.jN u (R.eNu u (Pi.single i 1))) = D.eMu u φ := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_smul, ← map_sum]
  rw [sum_coord_jN]

theorem sum_coord_heq (M : Seam R cr) (u w : D.what₂.Word) (hw : w = u)
    (b : Fin ((fc X.zs).Dc.a (R.wU u)) → (D.mem w).A.Mram)
    (hb : ∀ i, HEq (b i) (D.eMu u (D.jN u (R.eNu u (Pi.single i 1))))) (φ : D.what₂.Mu u) :
    HEq (∑ i, M.cφ u φ i • b i) (D.eMu u φ) := by
  subst hw
  have : b = fun i => D.eMu w (D.jN w (R.eNu w (Pi.single i 1))) := funext fun i => eq_of_heq (hb i)
  subst this
  exact heq_of_eq (sum_coord_eMu M w φ)

theorem inner_tw_of_smul {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) (x y : Tw s E) (κ₀ : ℂ) (v : E)
    (hx : Tw.out x = κ₀ • v) : ⟪x, y⟫_ℂ = cj s (starRingEnd ℂ κ₀ * ⟪v, Tw.out y⟫_ℂ) := by
  rw [Tw.inner_eq, hx, inner_smul_left]

end GlobalTheory.Mem.SJ.Pair

end
end

