module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.OneBlockCell

def valEquiv {β : Type} {n : β → ℕ} {t : ℕ} (a₀ : β) (ha₀ : n a₀ = t) (h0 : ∀ j, j ≠ a₀ → n j = 0) :
    (Σ j, Fin (n j)) ≃ Fin t where
  toFun p := ⟨p.2.val, by
    by_cases hp : p.1 = a₀
    · have h1 := p.2.2
      have h2 : n p.1 = t := hp ▸ ha₀
      omega
    · have h1 := p.2.2
      have h2 := h0 _ hp
      omega⟩
  invFun x := ⟨a₀, ⟨x.val, by have := x.2; omega⟩⟩
  left_inv p := by
    obtain ⟨a, s⟩ := p
    by_cases ha : a = a₀
    · subst ha
      rfl
    · have h1 := s.2
      have h2 := h0 _ ha
      omega
  right_inv x := rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deltaHalf_eq_one_of_single {β : Type} [Fintype β] [LinearOrder β] {n : β → ℕ} (a₀ : β)
    (h0 : ∀ j, j ≠ a₀ → n j = 0) (g : Levi k (fun j => Fin (n j))) :
    deltaHalf k (fun j => Fin (n j)) g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  by_cases ha : a = a₀
  · subst ha
    have hs : ∀ s : Finset β, a ∉ s → ∑ b ∈ s, (Fintype.card (Fin (n b)) : ℤ) = 0 := fun s hs =>
      Finset.sum_eq_zero fun b hb => by
        have hba : b ≠ a := fun e => hs (e ▸ hb)
        simp [h0 b hba]
    have hm : modExp (fun j => Fin (n j)) a = 0 := by
      unfold modExp
      rw [hs _ (by simp), hs _ (by simp), sub_zero]
    rw [hm]
    simp
  · haveI : IsEmpty (Fin (n a)) := ⟨fun x => absurd x.2 (by have := x.2; have := h0 a ha; omega)⟩
    have : Matrix.GeneralLinearGroup.det (g a) = 1 := by
      ext
      simp [Matrix.det_isEmpty]
    rw [this, map_one]

theorem mem_parab_of_single {R : Type} [CommRing R] {β : Type} [LinearOrder β] {n : β → ℕ} {t : ℕ}
    (e : (Σ j, Fin (n j)) ≃ Fin t) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → n j = 0) (x : GL (Fin t) R) :
    x ∈ parab R e := by
  refine mem_parab_iff.2 fun a b i j hab => ?_
  by_cases ha : a = a₀
  · have hb : b ≠ a₀ := fun e => by rw [e, ha] at hab; exact lt_irrefl _ hab
    exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

theorem eq_one_of_mem_unipRad_single {R : Type} [CommRing R] {β : Type} [Fintype β] [LinearOrder β]
    {n : β → ℕ} {t : ℕ} (e : (Σ j, Fin (n j)) ≃ Fin t) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → n j = 0)
    {g : GL (Fin t) R} (hg : g ∈ unipRad R e) : g = 1 := by
  obtain ⟨-, h2⟩ := mem_unipRad.1 hg
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  by_cases ha : a = a₀
  · by_cases hb : b = a₀
    · obtain rfl : b = a := hb.trans ha.symm
      rw [h2 b i j]
      simp [Matrix.one_apply]
    · exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

open scoped TensorProduct

theorem reindex_piTensor {d : Fin 2 → ℕ} (σ : ∀ i, Irr k (d i)) (γ : ∀ i, GL (Fin (d i)) k)
    (p : ∀ j, GL (Fin (d (Equiv.swap 0 1 j))) k) (h : ∀ j, γ (Equiv.swap 0 1 j) = p j)
    (y : ⨂[ℂ] i, (σ i).V) :
    PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1) ((piTensor fun i => (σ i).π) γ y) =
      (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p
        (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1) y) := by
  suffices H : (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)).toLinearMap ∘ₗ
      (piTensor fun i => (σ i).π) γ = (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p ∘ₗ
      (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)).toLinearMap from
    LinearMap.congr_fun H y
  refine PiTensorProduct.ext (MultilinearMap.ext fun z => ?_)
  have e1 : (((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p ∘ₗ
      (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)).toLinearMap).compMultilinearMap
        (PiTensorProduct.tprod ℂ)) z = (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p
          (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1) (PiTensorProduct.tprod ℂ z)) := rfl
  have e2 := PiTensorProduct.reindex_tprod (R := ℂ) (s := fun i => (σ i).V) (Equiv.swap 0 1) z
  have e3 := piTensor_tprod (fun j => (σ (Equiv.swap 0 1 j)).π) p (fun j => z (Equiv.swap 0 1 j))
  refine Eq.trans ?_ e1.symm
  refine Eq.trans ?_ (congrArg (fun w => (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p w) e2).symm
  refine Eq.trans ?_ e3.symm
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    piTensor_tprod, PiTensorProduct.reindex_tprod]
  refine congrArg (PiTensorProduct.tprod ℂ (s := fun j => (σ (Equiv.swap 0 1 j)).V)) (funext fun j => ?_)
  show (σ (Equiv.swap 0 1 j)).π (γ (Equiv.swap 0 1 j)) (z (Equiv.swap 0 1 j)) = _
  rw [h j]

theorem cellFunctor_swap_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)), d 1 = 1 →
    ∀ (b : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j)))), b.1 1 0 = 1 →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j))),
      Nonempty ((cellFunctor f g (piTensor fun i => (σ i).π)).Equiv
        (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)) := by
  intro k _ _ _ _ d σ hd b hb
  have r0 := b.2.1 0
  have r1 := b.2.1 1
  have c0 := b.2.2 0
  have c1 := b.2.2 1
  simp only [Fin.sum_univ_two, Fintype.card_fin, Equiv.swap_apply_left, Equiv.swap_apply_right] at r0 r1 c0 c1
  have h00 : b.1 0 0 = 0 := by omega
  have h11 : b.1 1 1 = 0 := by omega
  have hrz : ∀ i j, j ≠ Equiv.swap 0 1 i → b.1 i j = 0 := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp_all
  have hcz : ∀ j i, i ≠ Equiv.swap 0 1 j → b.1 i j = 0 := by
    intro j i hi
    fin_cases i <;> fin_cases j <;> simp_all
  have hrf : ∀ i, b.1 i (Equiv.swap 0 1 i) = d i := by
    intro i
    fin_cases i <;> simp <;> omega
  have hcf : ∀ j, b.1 (Equiv.swap 0 1 j) j = d (Equiv.swap 0 1 j) := by
    intro j
    fin_cases j <;> simp <;> omega

  let f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i) := fun i =>
    valEquiv (Equiv.swap 0 1 i) (hrf i) (fun j hj => hrz i j hj)
  let g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j)) := fun j =>
    valEquiv (Equiv.swap 0 1 j) (hcf j) (fun i hi => hcz j i hi)
  refine ⟨f, g, ?_⟩
  have hbot : twKer (piTensor fun i => (σ i).π) (relUnip k f) 1 = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    have : (n : Levi k (fun i => Fin (d i))) = 1 := funext fun i =>
      eq_one_of_mem_unipRad_single (f i) (Equiv.swap 0 1 i) (fun j hj => hrz i j hj) (n.2 i trivial)
    simp [this]
  have hδ : ∀ z, relDeltaHalf k (fun i j => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ =>
      deltaHalf_eq_one_of_single (Equiv.swap 0 1 i) (fun j hj => hrz i j hj) (z i)
  have hδ' : ∀ z, relDeltaHalf k (fun j i => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun j _ =>
      deltaHalf_eq_one_of_single (Equiv.swap 0 1 j) (fun i hi => hcz j i hi) (z j)
  have hP : ∀ x, x ∈ relParab k g := fun x j _ =>
    mem_parab_of_single (g j) (Equiv.swap 0 1 j) (fun i hi => hcz j i hi) (x j)
  have hγ : ∀ (p : relParab k g) j,
      relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g p)) (Equiv.swap 0 1 j) =
        (p : Levi k (fun j => Fin (d (Equiv.swap 0 1 j)))) j := by
    intro p j
    rw [relEmb_apply]
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, t⟩, rfl⟩ := (f (Equiv.swap 0 1 j)).surjective x
    obtain ⟨⟨a', s⟩, rfl⟩ := (f (Equiv.swap 0 1 j)).surjective y
    have ha : a = j := by
      by_contra hne
      have h1 := hrz (Equiv.swap 0 1 j) a (by rwa [Equiv.swap_apply_self])
      have h2 := t.2
      omega
    have ha' : a' = j := by
      by_contra hne
      have h1 := hrz (Equiv.swap 0 1 j) a' (by rwa [Equiv.swap_apply_self])
      have h2 := s.2
      omega
    subst ha
    subst ha'
    rw [leviEmb_apply_same]
    rfl

  have hsm : IsSmooth (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) :=
    isSmooth_piTensor fun j => (σ (Equiv.swap 0 1 j)).smooth
  let R := PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)
  let Ψ : (⨂[ℂ] j, (σ (Equiv.swap 0 1 j)).V) ≃ₗ[ℂ]
      Jacquet (piTensor fun i => (σ i).π) (relUnip k f) :=
    R.symm.trans (Submodule.quotEquivOfEqBot _ hbot).symm
  have hΨ : ∀ u, Ψ u = Submodule.Quotient.mk (R.symm u) := fun u => rfl
  let τ := (twist ((relJac f (piTensor fun i => (σ i).π)).comp (swapBlocks k (fun i j => Fin (b.1 i j))))
        (relDeltaHalf k (fun j i => Fin (b.1 i j)))).comp (relProj k g)
  have law : ∀ (p : relParab k g) u, τ p (Ψ u) =
        Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p u) := by
    intro p u
    rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, hΨ, relJac_mk, hδ, hδ', hΨ]
    simp only [inv_one, Units.val_one, one_smul]
    congr 1
    apply R.injective
    rw [reindex_piTensor σ _ (p : Levi k (fun j => Fin (d (Equiv.swap 0 1 j)))) (hγ p)]
    exact (congrArg (fun w => (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)
      (p : Levi k (fun j => Fin (d (Equiv.swap 0 1 j)))) w) (R.apply_symm_apply u)).trans
        (R.apply_symm_apply _).symm
  let F : (piTensor fun j => (σ (Equiv.swap 0 1 j)).π).IntertwiningMap
      (cellFunctor f g (piTensor fun i => (σ i).π)) :=
    { toFun := fun u => ⟨⟨fun x => Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x u), fun p x => by
          show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) (↑p * x) u) = _
          rw [map_mul, Module.End.mul_apply]
          exact (law p _).symm⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm u).mem_nhds (by simp)) fun x hx => by
          have hx' : (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x u = u := hx
          refine Subtype.ext (funext fun y => ?_)
          show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) (y * x) u) =
            Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) y u)
          rw [map_mul, Module.End.mul_apply, hx'])⟩
      map_add' := fun u w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c u => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun h => LinearMap.ext fun u => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x
            ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) h u)) =
          Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) (x * h) u)
        rw [map_mul, Module.End.mul_apply])) }
  refine ⟨(LocGL.equivOfBijective F ⟨fun u w hw => ?_, fun φ => ⟨Ψ.symm (φ.1.1 1),
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩).symm⟩
  · have h1 : Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) 1 u) =
        Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) 1 w) := congrArg (fun φ => φ.1.1 1) hw
    simpa using h1
  · show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x (Ψ.symm (φ.1.1 1))) = φ.1.1 x
    refine (law ⟨x, hP x⟩ (Ψ.symm (φ.1.1 1))).symm.trans ?_
    refine (congrArg (τ ⟨x, hP x⟩) (Ψ.apply_symm_apply (φ.1.1 1))).trans ?_
    refine (φ.1.2 ⟨x, hP x⟩ 1).symm.trans ?_
    exact congrArg φ.1.1 (mul_one x)

end GlobalTheory.OneBlockCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeDEqSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeRecon

section SlopeTestRemainingChoices
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem rt_rt {W : Type} [AddCommGroup W] [Module ℂ W] (h h' : GAf L n) (f : GAf L n → W) :
    NG.rt L n h' (NG.rt L n h f) = NG.rt L n (h' * h) f := by
  funext g
  change f (g * h' * h) = f (g * (h' * h))
  rw [mul_assoc]

theorem rt_one {W : Type} [AddCommGroup W] [Module ℂ W] (f : GAf L n → W) : NG.rt L n 1 f = f := by
  funext g
  change f (g * 1) = f g
  rw [mul_one]

theorem finite_cosets (N' : ℕ) (hN' : 0 < N') :
    {c : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N' | ∃ x : GAf L n, x ∈ Umax L n ∧
      (x : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N') = c}.Finite := by
  classical
  obtain ⟨Q, hQ, c, hc⟩ := GlobalTheory.IsotOrth.exists_finite_class (F := NumberField.maximalRealSubfield L) (E := L) N' hN'
  haveI := hQ
  let cls : Umax L n → Fin n → Fin n → Q := fun κ i j => c ⟨(κ.1.1 : Matrix (Fin n) (Fin n) (AL L)) i j, κ.2 i j⟩
  have key : ∀ a b : Umax L n, cls a = cls b →
      ((a.1 : GAf L n) : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N') = (b.1 : GAf L n) := by
    intro a b hab
    rw [QuotientGroup.eq]
    exact GlobalTheory.IsotOrth.cong_inv_mul a.2 b.2 (fun i j => by
      obtain ⟨z, hz⟩ := hc _ _ (congrFun (congrFun hab i) j).symm
      refine ⟨z.1, z.2, ?_⟩
      simpa using congrArg Subtype.val hz)
  let F : (Fin n → Fin n → Q) → GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N' := fun q =>
    if h : ∃ a, cls a = q then ((h.choose.1 : GAf L n) : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N') else ((1 : GAf L n) : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n N')
  refine (Set.finite_range F).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨cls ⟨x, hx⟩, ?_⟩
  have h : ∃ a, cls a = cls ⟨x, hx⟩ := ⟨_, rfl⟩
  simp only [F, dif_pos h]
  exact key _ _ h.choose_spec

open Classical in
theorem heckeD_eq_sum {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf L n)) (D : Set (GAf L n))
    (hfin : {c : GAf L n ⧸ J | ∃ x ∈ D, (x : GAf L n ⧸ J) = c}.Finite) (f : GAf L n → W) (g : GAf L n) :
    NG.heckeD J D f g = ∑ c ∈ hfin.toFinset,
      (if hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = c then f (g * hc.choose) else 0) := by
  unfold NG.heckeD
  rw [finsum_eq_sum_of_support_subset]
  intro c hc
  rw [Set.Finite.coe_toFinset]
  by_contra h
  exact hc (dif_neg h)

theorem heckeD_add {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf L n)) (D : Set (GAf L n))
    (hfin : {c : GAf L n ⧸ J | ∃ x ∈ D, (x : GAf L n ⧸ J) = c}.Finite) (f f' : GAf L n → W) :
    NG.heckeD J D (f + f') = NG.heckeD J D f + NG.heckeD J D f' := by
  funext g
  rw [Pi.add_apply, heckeD_eq_sum J D hfin, heckeD_eq_sum J D hfin, heckeD_eq_sum J D hfin, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem heckeD_smul {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf L n)) (D : Set (GAf L n))
    (hfin : {c : GAf L n ⧸ J | ∃ x ∈ D, (x : GAf L n ⧸ J) = c}.Finite) (a : ℂ) (f : GAf L n → W) :
    NG.heckeD J D (a • f) = a • NG.heckeD J D f := by
  funext g
  rw [Pi.smul_apply, heckeD_eq_sum J D hfin, heckeD_eq_sum J D hfin, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem heckeD_zero {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf L n)) (D : Set (GAf L n)) :
    NG.heckeD J D (0 : GAf L n → W) = 0 := by
  funext g
  simp [NG.heckeD]

theorem heckeD_one {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf L n)) (v : GAf L n → W)
    (hv : ∀ κ ∈ J, NG.rt L n κ v = v) :
    NG.heckeD J {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * 1 * u'} v = v := by
  funext g
  unfold NG.heckeD
  rw [finsum_eq_single _ ((1 : GAf L n) : GAf L n ⧸ J)]
  · have h : ∃ x ∈ {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * 1 * u'},
        (x : GAf L n ⧸ J) = ((1 : GAf L n) : GAf L n ⧸ J) :=
      ⟨1, ⟨1, J.one_mem, 1, J.one_mem, by simp⟩, rfl⟩
    rw [dif_pos h]
    obtain ⟨⟨u, hu, u', hu', e⟩, -⟩ := h.choose_spec
    rw [e]
    have : u * 1 * u' ∈ J := by simpa using J.mul_mem hu hu'
    exact congrFun (hv _ this) g
  · intro c hc
    rw [dif_neg]
    rintro ⟨x, ⟨u, hu, u', hu', rfl⟩, hx⟩
    apply hc
    rw [← hx, QuotientGroup.eq]
    have : u * 1 * u' ∈ J := by simpa using J.mul_mem hu hu'
    simpa using J.inv_mem this

end SlopeTestRemainingChoices

theorem recon : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a b : NG.AlgWt L n) (S₁ : Submodule ℂ (GAf L n → a.W)) (S₂ : Submodule ℂ (GAf L n → b.W)), NG.IsIrrRep a.ρ S₁ → NG.IsIrrRep b.ρ S₂ → ∀ N : ℕ, 0 < N → ∀ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → b.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) → (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) → NG.IsoRep S₁ S₂ := by
  intro L _ _ _ n a b S₁ S₂ hS₁ hS₂ N hN φ hφ hex hT
  obtain ⟨f₀, hf₀S, hf₀fix, hf₀ne⟩ := hex
  set J := GlobalTheory.IsotOrth.congSub L n N with hJ
  let gens : Set ((GAf L n → a.W) × (GAf L n → b.W)) :=
    {w | ∃ (h : GAf L n) (f : GAf L n → a.W), f ∈ S₁ ∧ (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧
      w = (NG.rt L n h f, NG.rt L n h (φ f))}
  let W := Submodule.span ℂ gens
  have hgen : ∀ (h : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) →
      (NG.rt L n h f, NG.rt L n h (φ f)) ∈ W := fun h f hf hfix => Submodule.subset_span ⟨h, f, hf, hfix, rfl⟩
  have hWS : ∀ w ∈ W, w.1 ∈ S₁ ∧ w.2 ∈ S₂ := by
    intro w hw
    have : W ≤ S₁.prod S₂ := by
      rw [Submodule.span_le]
      rintro _ ⟨h, f, hf, hfix, rfl⟩
      exact ⟨hS₁.1.stable h f hf, hS₂.1.stable h _ (hφ f hf hfix).1⟩
    exact this hw
  have hWst : ∀ h, ∀ w ∈ W, (NG.rt L n h w.1, NG.rt L n h w.2) ∈ W := by
    intro h w hw
    have : W ≤ W.comap ((NG.rt L n h).prodMap (NG.rt L n h)) := by
      rw [Submodule.span_le]
      rintro _ ⟨h', f, hf, hfix, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.prodMap_apply, rt_rt, rt_rt]
      exact hgen _ f hf hfix
    exact this hw
  have hfinE : ∀ M', 0 < M' → {c : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M') |
      ∃ x ∈ (J : Set (GAf L n)), (x : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M')) = c}.Finite := by
    intro M' hM'
    refine (finite_cosets (N * M') (Nat.mul_pos hN hM')).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, (show NG.Cong L n N x from hx).1, rfl⟩
  let P : ((GAf L n → a.W) × (GAf L n → b.W)) → Prop := fun w => ∃ M : ℕ, 0 < M ∧ ∀ M', 0 < M' → M ∣ M' →
    NG.heckeD (GlobalTheory.IsotOrth.congSub L n (N * M')) (J : Set (GAf L n)) w.2 =
      φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n (N * M')) (J : Set (GAf L n)) w.1)
  let Good : Submodule ℂ ((GAf L n → a.W) × (GAf L n → b.W)) :=
    { carrier := {w | P w}
      zero_mem' := ⟨1, one_pos, fun M' _ _ => by simp [heckeD_zero]⟩
      add_mem' := by
        rintro w w' ⟨M, hM, hw⟩ ⟨M₁, hM₁, hw'⟩
        refine ⟨M * M₁, Nat.mul_pos hM hM₁, fun M' hM' hd => ?_⟩
        have h1 := hw M' hM' (dvd_trans (dvd_mul_right M M₁) hd)
        have h2 := hw' M' hM' (dvd_trans (dvd_mul_left M₁ M) hd)
        simp only [Prod.fst_add, Prod.snd_add]
        rw [heckeD_add _ _ (hfinE M' hM'), heckeD_add _ _ (hfinE M' hM'), h1, h2, map_add (f := _)]
      smul_mem' := by
        rintro c w ⟨M, hM, hw⟩
        refine ⟨M, hM, fun M' hM' hd => ?_⟩
        simp only [Prod.smul_fst, Prod.smul_snd]
        rw [heckeD_smul _ _ (hfinE M' hM'), heckeD_smul _ _ (hfinE M' hM'), hw M' hM' hd, map_smul] }
  have hWG : W ≤ Good := by
    rw [Submodule.span_le]
    rintro _ ⟨h, f, hf, hfix, rfl⟩
    obtain ⟨M, hM, hMc⟩ := _root_.GlobalTheory.ConjCong.exists_cong_conj L n N h hN
    refine ⟨M, hM, fun M' hM' hd => ?_⟩
    obtain ⟨k, rfl⟩ := hd
    have hconj : ∀ κ ∈ GlobalTheory.IsotOrth.congSub L n (N * (M * k)), h⁻¹ * κ * h ∈ J := by
      intro κ hκ
      rw [← mul_assoc] at hκ
      exact hMc κ (NG.Cong.of_mul_left L n hκ)
    have hle : GlobalTheory.IsotOrth.congSub L n (N * (M * k)) ≤ J := fun κ hκ => NG.Cong.of_mul_left L n hκ
    obtain ⟨m, -, hmE⟩ := _root_.GlobalTheory.HeckeAverage.heckeD_rt_eq_smul L n J (GlobalTheory.IsotOrth.congSub L n (N * (M * k))) h hle hconj (hfinE _ hM')
    have hfixJ : ∀ κ ∈ J, NG.rt L n κ f = f := fun κ hκ => hfix κ hκ
    have hφfixJ : ∀ κ ∈ J, NG.rt L n κ (φ f) = φ f := fun κ hκ => (hφ f hf hfix).2 κ hκ
    show NG.heckeD _ _ (NG.rt L n h (φ f)) = φ (NG.heckeD _ _ (NG.rt L n h f))
    rw [hmE _ f hfixJ, hmE _ (φ f) hφfixJ, map_smul, hT h f hf hfix]
  have hWP : ∀ w ∈ W, P w := fun w hw => hWG hw
  have hK2 : ∀ u, ((0 : GAf L n → a.W), u) ∈ W → u = 0 := by
    let K : Submodule ℂ (GAf L n → b.W) := W.comap (LinearMap.inr ℂ _ _)
    have hKsub : NG.IsSubrep b.ρ K := ⟨fun u hu => hS₂.1.le (hWS _ hu).2, fun h u hu => by
      have := hWst h _ hu
      simpa [K] using this⟩
    have hKle : K ≤ S₂ := fun u hu => (hWS _ hu).2
    rcases hS₂.2.2 K hKsub hKle with hK | hK
    · intro u hu
      have : u ∈ K := hu
      rwa [hK, Submodule.mem_bot] at this
    · exfalso
      have hmem : φ f₀ ∈ K := hK ▸ (hφ f₀ hf₀S hf₀fix).1
      obtain ⟨M, hM, hMg⟩ := hWP _ (Submodule.mem_comap.1 hmem)
      have e := hMg M hM dvd_rfl
      obtain ⟨m, hm, hmE⟩ := _root_.GlobalTheory.HeckeAverage.heckeD_rt_eq_smul L n J (GlobalTheory.IsotOrth.congSub L n (N * M)) 1
        (fun κ hκ => NG.Cong.of_mul_left L n hκ)
        (fun κ hκ => by rw [inv_one, one_mul, mul_one]; exact NG.Cong.of_mul_left L n hκ) (hfinE M hM)
      have hφfixJ : ∀ κ ∈ J, NG.rt L n κ (φ f₀) = φ f₀ := fun κ hκ => (hφ f₀ hf₀S hf₀fix).2 κ hκ
      have e2 := hmE _ (φ f₀) hφfixJ
      rw [rt_one, heckeD_one J _ hφfixJ] at e2
      simp only [LinearMap.inr_apply, heckeD_zero, map_zero] at e
      rw [e] at e2
      apply hf₀ne
      have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      exact (smul_eq_zero.1 e2.symm).resolve_left hm'
  have hK1 : ∀ u, (u, (0 : GAf L n → b.W)) ∈ W → u = 0 := by
    let K : Submodule ℂ (GAf L n → a.W) := W.comap (LinearMap.inl ℂ _ _)
    have hKsub : NG.IsSubrep a.ρ K := ⟨fun u hu => hS₁.1.le (hWS _ hu).1, fun h u hu => by
      have := hWst h _ hu
      simpa [K] using this⟩
    have hKle : K ≤ S₁ := fun u hu => (hWS _ hu).1
    rcases hS₁.2.2 K hKsub hKle with hK | hK
    · intro u hu
      have : u ∈ K := hu
      rwa [hK, Submodule.mem_bot] at this
    · exfalso
      have hmem : f₀ ∈ K := hK ▸ hf₀S
      have h1 : (f₀, (0 : GAf L n → b.W)) ∈ W := hmem
      have h2 := hgen 1 f₀ hf₀S hf₀fix
      rw [rt_one, rt_one] at h2
      have h3 := W.sub_mem h2 h1
      simp only [Prod.mk_sub_mk, sub_self, sub_zero] at h3
      exact hf₀ne (hK2 _ h3)
  refine _root_.GlobalTheory.isoRep_of_stable_graph L n a.ρ b.ρ S₁ S₂ W hS₁ hS₂ hWS hWst hK2 hK1 ?_
  intro hbot
  have := hgen 1 f₀ hf₀S hf₀fix
  rw [hbot, Submodule.mem_bot, rt_one, rt_one] at this
  exact hf₀ne (congrArg Prod.snd this)

end GlobalTheory.HeckeRecon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientParIndProductsFlattenedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotient_parInd_products_flattened : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (X a b)] [∀ a b, Module ℂ (X a b)] (ρ : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (X a b)), (∀ a b, IsSmooth (ρ a b)) → ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n, IsSubquotient (multiProd e fun a => multiProd (e' a) (ρ a)) (multiProd E fun c => ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) := by
  first | exact @GlobalTheory.SmGL.Stages.isSubquotient_multiProd_multiProd | exact GlobalTheory.SmGL.Stages.isSubquotient_multiProd_multiProd | (intros; apply GlobalTheory.SmGL.Stages.isSubquotient_multiProd_multiProd <;> assumption)
end

