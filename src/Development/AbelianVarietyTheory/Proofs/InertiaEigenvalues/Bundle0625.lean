module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0602
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0198

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivLocProdTriv
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem infGL_mem_UA {n : ℕ} (y : GL (Fin n) (Cinf E)) (hy : y.valᴴ * y.val = 1) : infGL E n y ∈ UA E n := by
  change cT (conjAd E) (infGL E n y).val * 1 * (infGL E n y).val = 1
  have h1 : (infGL E n y).val.map (pInf E) = y.val := congrArg Units.val (pInf_infGL y)
  have h2 : (infGL E n y).val.map (pFin E) = 1 := congrArg Units.val (pFin_infGL y)
  have h3 : (cT (conjAd E) (infGL E n y).val).map (pInf E) = y.valᴴ := by
    ext1 i j
    rw [Matrix.conjTranspose_apply, ← h1]
    exact (infEq E).symm_apply_apply _
  have h4 : (cT (conjAd E) (infGL E n y).val).map (pFin E) = 1 := by
    ext1 i j
    change conjFin (IsCMField.complexConj E).toRingEquiv (((infGL E n y).val.map (pFin E)) j i) = _
    rw [h2]
    simp only [Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have h5 := congrArg₂ (· * ·) h3 h1
  have h6 := congrArg₂ (· * ·) h4 h2
  simp only [← Matrix.map_mul, hy, mul_one] at h5 h6
  rw [mul_one]
  ext1 i j
  refine ad_ext ((congrFun₂ h5 i j).trans ?_) ((congrFun₂ h6 i j).trans ?_) <;>
  · simp only [Matrix.one_apply]
    split_ifs <;> simp


end GlobalTheory.UnitaryBC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivProdChosenIrrGLPairDegreeZero
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.LocGL

theorem exists_linearEquiv_of_subsingleton {G V : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) : Nonempty (V ≃ₗ[ℂ] ℂ) := by
  have hst : ∀ (U : Submodule ℂ V) (g : G) ⦃v : V⦄, v ∈ U → π g v ∈ U := fun U g v hv => by
    rw [Subsingleton.elim g 1, map_one]
    exact hv
  have := hi
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
    apply Subrepresentation.ext
    ext w
    rw [h w]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  have htop : Submodule.span ℂ {v} = ⊤ := by
    rcases eq_bot_or_eq_top (⟨Submodule.span ℂ {v}, hst _⟩ : Subrepresentation π) with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp (congrArg Subrepresentation.toSubmodule h)) hv
    · exact congrArg Subrepresentation.toSubmodule h
  exact ⟨((LinearEquiv.toSpanNonzeroSingleton ℂ V v hv).trans (LinearEquiv.ofTop _ htop)).symm⟩

theorem exists_equiv_piTensor_two {X : Fin 2 → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (f : X 1 ≃ₗ[ℂ] ℂ) : ∃ (b : ∀ a, X a) (L : X 0 ≃ₗ[ℂ] PiTensorProduct ℂ X),
      ∀ v, L v = PiTensorProduct.tprod ℂ (Function.update b 0 v) := by
  classical
  let b : ∀ a, X a := Pi.single 1 (f.symm 1)
  have hb : b 1 = f.symm 1 := Pi.single_eq_same _ _
  let μ : MultilinearMap (RingHom.id ℂ) X (X 0) :=
    { toFun := fun x => f (x 1) • x 0
      map_update_add' := by
        intro _ x i p q
        fin_cases i
        · simp only [Fin.zero_eta, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true,
            Function.update_of_ne, smul_add]
        · simp only [Fin.mk_one, Function.update_self, ne_eq, zero_ne_one, not_false_eq_true,
            Function.update_of_ne, map_add, add_smul]
      map_update_smul' := by
        intro _ x i c p
        fin_cases i
        · simp only [Fin.zero_eta, Function.update_self, ne_eq, one_ne_zero, not_false_eq_true,
            Function.update_of_ne, RingHom.id_apply, smul_comm (f (x 1)) c]
        · simp only [Fin.mk_one, Function.update_self, ne_eq, zero_ne_one, not_false_eq_true,
            Function.update_of_ne, map_smul, smul_eq_mul, mul_smul, RingHom.id_apply] }
  have hμ : ∀ x, μ x = f (x 1) • x 0 := fun _ => rfl
  let φ : X 0 →ₗ[ℂ] PiTensorProduct ℂ X := (PiTensorProduct.tprod ℂ).toLinearMap b 0
  have hφ : ∀ v, φ v = PiTensorProduct.tprod ℂ (Function.update b 0 v) := fun _ => rfl
  refine ⟨b, LinearEquiv.ofLinearMap φ (PiTensorProduct.lift μ) ?_ ?_, hφ⟩
  · apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      PiTensorProduct.lift.tprod, hμ, hφ, LinearMap.id_coe, id_eq]
    have hx : x = Function.update (Function.update b 0 (x 0)) 1
        (f (x 1) • Function.update b 0 (x 0) 1) := by
      funext a
      fin_cases a
      · simp
      · simp only [Fin.mk_one, Function.update_self]
        rw [Function.update_of_ne (by decide), hb, ← map_smul, smul_eq_mul, mul_one,
          LinearEquiv.symm_apply_apply]
    conv_rhs => rw [hx]
    rw [MultilinearMap.map_update_smul (PiTensorProduct.tprod ℂ) b 0,
      MultilinearMap.map_update_smul (PiTensorProduct.tprod ℂ) (Function.update b 0 (x 0)) 1,
      Function.update_eq_self]
  · apply LinearMap.ext
    intro v
    simp only [LinearMap.coe_comp, Function.comp_apply, hφ, PiTensorProduct.lift.tprod, hμ,
      LinearMap.id_coe, id_eq, Function.update_self]
    rw [Function.update_of_ne (by decide), hb, LinearEquiv.apply_symm_apply, one_smul]

private theorem mem_parab_of_isEmpty_second_block {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : Fin 2 → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [IsEmpty (m 1)] (e : (Σ a, m a) ≃ m 0) (g : GL (m 0) k) : g ∈ parab k e := by
  have hb : ∀ x : m 0, blk e x = 0 := by
    intro x
    unfold blk
    generalize e.symm x = s
    obtain ⟨a, y⟩ := s
    obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    · rfl
    · exact isEmptyElim y
  rw [mem_parab]
  intro i j hij
  rw [hb i, hb j] at hij
  exact absurd hij (lt_irrefl _)

private theorem leviProj_zero_eq_coe {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : Fin 2 → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (e : (Σ a, m a) ≃ m 0) (he : ∀ i, e ⟨0, i⟩ = i) (p : parab k e) :
    leviProj k e p 0 = (p : GL (m 0) k) :=
  Units.ext (Matrix.ext fun i j => by rw [leviProj_apply, he, he])

private theorem deltaHalf_eq_one_of_isEmpty_second_block {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : Fin 2 → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [IsEmpty (m 1)] (g : Levi k m) : deltaHalf k m g = 1 := by
  have : Subsingleton (GL (m 1) k) := ⟨fun a b => Units.ext (Matrix.ext fun i => isEmptyElim i)⟩
  have h0 : modExp m 0 = 0 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two, Fintype.card_eq_zero]
  have h1 : g 1 = 1 := Subsingleton.elim _ _
  rw [deltaHalf_apply, Fin.prod_univ_two, h0, h1, map_one, map_one, mul_one]
  simp [absPow_zero]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nonempty_equiv_multiProd_empty {m : Fin 2 → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [IsEmpty (m 1)] {X : Fin 2 → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    {π : ∀ a, Representation ℂ (GL (m a) k) (X a)} (hπ : IsSmooth (π 0)) (hi : (π 1).IsIrreducible)
    (e : (Σ a, m a) ≃ m 0) (he : ∀ i, e ⟨0, i⟩ = i) : Nonempty ((π 0).Equiv (multiProd e π)) := by
  have : Subsingleton (GL (m 1) k) := ⟨fun a b => Units.ext (Matrix.ext fun i => isEmptyElim i)⟩
  obtain ⟨f₁⟩ := exists_linearEquiv_of_subsingleton hi
  obtain ⟨b, L, hL⟩ := exists_equiv_piTensor_two f₁
  have hσ : ∀ (p : parab k e) (u : X 0),
      (twist (piTensor π) (deltaHalf k m)) (leviProj k e p) (L u) = L (π 0 (p : GL (m 0) k) u) := by
    intro p u
    rw [twist_apply, deltaHalf_eq_one_of_isEmpty_second_block, Units.val_one, one_smul, hL, hL, piTensor_tprod]
    congr 1
    funext a
    obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    · rw [Function.update_self, Function.update_self, leviProj_zero_eq_coe e he]
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Subsingleton.elim (leviProj k e p 1) 1, map_one, Module.End.one_apply]
  have hval : ∀ (f : IndSp e (piTensor π)) (g : GL (m 0) k),
      f.1.1 g = L (π 0 g (L.symm (f.1.1 1))) := by
    intro f g
    have h := (f.1.2 : ∀ (h : parab k e) (x : GL (m 0) k), f.1.1 (h * x) = _) ⟨g, mem_parab_of_isEmpty_second_block e g⟩ 1
    rw [mul_one] at h
    have h' := hσ ⟨g, mem_parab_of_isEmpty_second_block e g⟩ (L.symm (f.1.1 1))
    rw [LinearEquiv.apply_symm_apply] at h'
    rw [h]
    exact h'
  let G : IndSp e (piTensor π) →ₗ[ℂ] X 0 :=
    L.symm.toLinearMap ∘ₗ LinearMap.proj 1 ∘ₗ (indSpace _ _).subtype ∘ₗ (smoothPart _).subtype
  have hG : ∀ f, G f = L.symm (f.1.1 1) := fun _ => rfl
  have hinj : Function.Injective G := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    rw [hG] at hf
    apply Subtype.ext
    apply Subtype.ext
    funext g
    rw [hval, hf, map_zero, map_zero]
    rfl
  have hsurj : Function.Surjective G := by
    intro v
    let F : GL (m 0) k → PiTensorProduct ℂ X := fun g => L (π 0 g v)
    have hF : F ∈ indSpace (parab k e) ((twist (piTensor π) (deltaHalf k m)).comp (leviProj k e)) := by
      intro p g
      show L (π 0 (p * g) v) = _
      rw [map_mul, Module.End.mul_apply, MonoidHom.comp_apply, hσ]
    have hS : (⟨F, hF⟩ : indSpace _ _) ∈ smoothPart (ind (parab k e)
        ((twist (piTensor π) (deltaHalf k m)).comp (leviProj k e))) := by
      have hset : {g' : GL (m 0) k | ind (parab k e) ((twist (piTensor π) (deltaHalf k m)).comp
          (leviProj k e)) g' ⟨F, hF⟩ = ⟨F, hF⟩} = {g' | π 0 g' v = v} := by
        ext g'
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro h
          have h1 := congrArg (fun φ : indSpace _ _ => φ.1 1) h
          have h2 : L (π 0 (1 * g') v) = L (π 0 1 v) := h1
          rw [one_mul, map_one, Module.End.one_apply] at h2
          exact L.injective h2
        · intro h
          apply Subtype.ext
          funext x
          show L (π 0 (x * g') v) = L (π 0 x v)
          rw [map_mul, Module.End.mul_apply, h]
      have hopen : IsOpen {g' : GL (m 0) k | ind (parab k e) ((twist (piTensor π) (deltaHalf k m)).comp
          (leviProj k e)) g' ⟨F, hF⟩ = ⟨F, hF⟩} := by
        rw [hset]
        exact hπ v
      exact hopen
    refine ⟨⟨⟨F, hF⟩, hS⟩, ?_⟩
    rw [hG]
    show L.symm (L (π 0 1 v)) = v
    rw [LinearEquiv.symm_apply_apply, map_one, Module.End.one_apply]
  refine ⟨(Representation.Equiv.mk (LinearEquiv.ofBijective G ⟨hinj, hsurj⟩) fun g => ?_).symm⟩
  apply LinearMap.ext
  intro f
  show G (multiProd e π g f) = π 0 g (G f)
  rw [hG, hG]
  rw [show ((multiProd e π g f).1.1 1) = f.1.1 g from by
    unfold multiProd
    rw [parInd_apply, one_mul]]
  rw [hval, LinearEquiv.symm_apply_apply]

theorem nonempty_equiv_prodIrr_two_zero (y : Fin 2 → IrrGL (k := k)) (hz : (y 1).1 = 0) (hd : ∑ a, (y a).1 = (y 0).1) :
    Nonempty ((y 0).rep.Equiv (prodIrr y hd)) := by
  have : IsEmpty (Fin (y 1).1) := by rw [hz]; infer_instance
  refine nonempty_equiv_multiProd_empty (m := fun a => Fin (y a).1) (X := fun a => (y a).2.rep.V)
    (π := fun a => (y a).rep) (y 0).2.rep.smooth (y 1).2.rep.irr _ fun i => ?_
  apply Fin.ext
  rw [stdBlocks_val]
  simp

theorem nonempty_equiv_prodIrr_pair_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x z : IrrGL (k := k)) (hz : z.1 = 0) (hd : ∑ a, (![x, z] a).1 = x.1) :
    Nonempty (x.rep.Equiv (prodIrr ![x, z] hd)) := nonempty_equiv_prodIrr_two_zero ![x, z] hz hd

end GlobalTheory.LocGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionCompGeneralLinearGroupMapOfFie
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil Matrix

namespace GlobalTheory.IndField

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

section Gen

variable {K₁ K₂ : Type} [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁] [IsNonarchimedeanLocalField K₁]
  [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂] [IsNonarchimedeanLocalField K₂]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def pullFun (e : (Σ a, m a) ≃ n) {ρ₁ : Representation ℂ (Levi K₁ m) W}
    {ρ₂ : Representation ℂ (Levi K₂ m) W}
    (s : GL n K₂ →* GL n K₁) (hs : Continuous s) (t : Levi K₂ m →* Levi K₁ m)
    (hP : ∀ p : parab K₂ e, s p ∈ parab K₁ e)
    (hL : ∀ p : parab K₂ e, leviProj K₁ e ⟨s p, hP p⟩ = t (leviProj K₂ e p))
    (hρ : ∀ L, ρ₂ L = ρ₁ (t L)) (hδ : ∀ L, deltaHalf K₁ m (t L) = deltaHalf K₂ m L) :
    IndSp e ρ₁ →ₗ[ℂ] IndSp e ρ₂ where
  toFun f := ⟨⟨fun x => f.1.1 (s x), fun p g => by
      show f.1.1 (s ((p : GL n K₂) * g)) =
        (deltaHalf K₂ m (leviProj K₂ e p) : ℂ) • ρ₂ (leviProj K₂ e p) (f.1.1 (s g))
      rw [map_mul, parInd_law e ρ₁ f ⟨s p, hP p⟩ (s g), hL, hδ, hρ]⟩, by
      apply mem_smoothPart_of_nhds
      have h1 : s ⁻¹' {g | ind (parab K₁ e) ((twist ρ₁ (deltaHalf K₁ m)).comp (leviProj K₁ e)) g f.1 = f.1}
          ∈ nhds (1 : GL n K₂) :=
        (f.2.preimage hs).mem_nhds (by simp)
      refine Filter.mem_of_superset h1 fun x hx => ?_
      refine Subtype.ext (funext fun y => ?_)
      show f.1.1 (s (y * x)) = f.1.1 (s y)
      rw [map_mul]
      exact congrArg (fun v : indSpace (parab K₁ e) ((twist ρ₁ (deltaHalf K₁ m)).comp (leviProj K₁ e)) =>
        (v : GL n K₁ → W) (s y)) hx⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Gen

section Gen2

variable {K₁ K₂ : Type} [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁] [IsNonarchimedeanLocalField K₁]
  [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂] [IsNonarchimedeanLocalField K₂]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def pullMap (e : (Σ a, m a) ≃ n) {ρ₁ : Representation ℂ (Levi K₁ m) W}
    {ρ₂ : Representation ℂ (Levi K₂ m) W}
    (s : GL n K₂ →* GL n K₁) (hs : Continuous s) (t : Levi K₂ m →* Levi K₁ m)
    (hP : ∀ p : parab K₂ e, s p ∈ parab K₁ e)
    (hL : ∀ p : parab K₂ e, leviProj K₁ e ⟨s p, hP p⟩ = t (leviProj K₂ e p))
    (hρ : ∀ L, ρ₂ L = ρ₁ (t L)) (hδ : ∀ L, deltaHalf K₁ m (t L) = deltaHalf K₂ m L) :
    Representation.IntertwiningMap ((parInd e ρ₁).comp s) (parInd e ρ₂) :=
  ⟨pullFun e s hs t hP hL hρ hδ, fun g => LinearMap.ext fun f =>
    Subtype.ext (Subtype.ext (funext fun x => by
      show f.1.1 (s x * s g) = f.1.1 (s (x * g))
      rw [map_mul]))⟩

end Gen2

section Map

variable {R S : Type} [CommRing R] [CommRing S]

def blockMap (φ : R →+* S) : Levi R m →* Levi S m :=
  MonoidHom.pi fun a => (GeneralLinearGroup.map φ).comp (Pi.evalMonoidHom (fun a => GL (m a) R) a)

@[simp] theorem blockMap_apply (φ : R →+* S) (L : Levi R m) (a : α) :
    blockMap φ L a = GeneralLinearGroup.map φ (L a) := rfl


omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in
theorem map_mem_parab (e : (Σ a, m a) ≃ n) (φ : R →+* S) (p : parab R e) :
    GeneralLinearGroup.map φ (p : GL n R) ∈ parab S e :=
  mem_parab.2 fun i j h => by
    change φ (((p : GL n R) : Matrix n n R) i j) = 0
    rw [mem_parab.1 p.2 i j h, map_zero]

theorem leviProj_map (e : (Σ a, m a) ≃ n) (φ : R →+* S) (p : parab R e) :
    leviProj S e ⟨GeneralLinearGroup.map φ (p : GL n R), map_mem_parab e φ p⟩ =
      blockMap φ (leviProj R e p) :=
  funext fun _ => Matrix.GeneralLinearGroup.ext fun _ _ => rfl

theorem continuous_glMap [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S]
    (φ : R →+* S) (hφ : Continuous φ) : Continuous (GeneralLinearGroup.map (n := n) φ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_map hφ : Continuous fun g : GL n R => (g : Matrix n n R).map φ)
  · have : (fun g : GL n R => (((GeneralLinearGroup.map φ g)⁻¹ : GL n S) : Matrix n n S)) =
        fun g => ((g⁻¹ : GL n R) : Matrix n n R).map φ := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_map hφ

end Map

theorem deltaHalf_blockMap {K₁ K₂ : Type} [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁]
    [IsNonarchimedeanLocalField K₁] [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂]
    [IsNonarchimedeanLocalField K₂] (φ : K₂ →+* K₁)
    (hn : ∀ y : K₂ˣ, nabs K₁ (Units.map φ.toMonoidHom y) = nabs K₂ y) (L : Levi K₂ m) :
    deltaHalf K₁ m (blockMap φ L) = deltaHalf K₂ m L := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => Units.ext ?_
  rw [val_absPow, val_absPow, blockMap_apply, GeneralLinearGroup.map_det]
  exact congrArg (fun r : ℝ => ((r : ℂ)) ^ _) (hn _)

theorem multiProd_comp_glMap : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i → Continuous i.symm → (∀ x : kˣ, GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x) → ∀ {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)), Nonempty (Representation.Equiv ((GlobalTheory.SmGL.multiProd e σ).comp (Matrix.GeneralLinearGroup.map (n := n) i.symm.toRingHom)) (GlobalTheory.SmGL.multiProd e fun a => (σ a).comp (Matrix.GeneralLinearGroup.map (n := m a) i.symm.toRingHom))) := by
  intro k k' _ _ _ _ _ _ _ _ i hi hi' hn α n m _ _ _ _ _ _ e X _ _ σ
  have hn' : ∀ y : k'ˣ, nabs k (Units.map i.symm.toRingHom.toMonoidHom y) = nabs k' y := fun y => by
    have h := hn (Units.map i.symm.toRingHom.toMonoidHom y)
    rw [show Units.map i.toRingHom.toMonoidHom (Units.map i.symm.toRingHom.toMonoidHom y) = y from
      Units.ext (by simp)] at h
    exact h.symm
  let Φ := pullMap e (ρ₁ := piTensor σ) (ρ₂ := piTensor fun a => (σ a).comp
      (GeneralLinearGroup.map (n := m a) i.symm.toRingHom))
    (GeneralLinearGroup.map i.symm.toRingHom) (continuous_glMap _ hi')
    (blockMap i.symm.toRingHom) (fun p => map_mem_parab e _ p) (fun p => leviProj_map e _ p)
    (fun _ => rfl) (fun L => deltaHalf_blockMap _ hn' L)
  let Ψ := pullFun e (ρ₁ := piTensor fun a => (σ a).comp
      (GeneralLinearGroup.map (n := m a) i.symm.toRingHom)) (ρ₂ := piTensor σ)
    (GeneralLinearGroup.map i.toRingHom) (continuous_glMap _ hi)
    (blockMap i.toRingHom) (fun p => map_mem_parab e _ p) (fun p => leviProj_map e _ p)
    (fun L => by
      show piTensor σ L = piTensor σ (fun a => GeneralLinearGroup.map i.symm.toRingHom
        (GeneralLinearGroup.map i.toRingHom (L a)))
      congr 1
      funext a
      ext
      simp) (fun L => deltaHalf_blockMap _ hn L)
  refine ⟨GlobalTheory.LocGL.equivOfBijective Φ (Function.bijective_iff_has_inverse.2 ⟨Ψ, fun f => ?_, fun f => ?_⟩)⟩
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (GeneralLinearGroup.map i.symm.toRingHom (GeneralLinearGroup.map i.toRingHom x)) = f.1.1 x
    rw [show GeneralLinearGroup.map i.symm.toRingHom (GeneralLinearGroup.map i.toRingHom x) = x from
      Matrix.GeneralLinearGroup.ext fun _ _ => by simp]
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom x)) = f.1.1 x
    rw [show GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom x) = x from
      Matrix.GeneralLinearGroup.ext fun _ _ => by simp]

end GlobalTheory.IndField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableCocycleOfFrobeniusMonodromyPair
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem GlobalTheory.semistable_class_of_pair : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ x ∈ Dst P ρ, ∀ y ∈ Dst P ρ, (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), c ∈ continuousCocycles ρ ∧ (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ monV P ℚ_[l] V z = x := by
  intro l _ P AI T K V _ _ _ _ _ _ _ ρ hρ x hx y hy hxy
  obtain ⟨ι, hιC, hιact⟩ := _root_.GlobalTheory.BstLog.iota_exists l P AI T
  obtain ⟨hιst, -, -⟩ := GlobalTheory.T.lTensor_semistable_to_deRham_equivariant l P ι hιC hιact K V ρ
  obtain ⟨z, hNz, hφz, hFz⟩ := GlobalTheory.T.exists_monodromy_frobenius_solution_fil l P AI T ι hιC K V x y hxy
  have hx' := (mem_Dst P ρ).mp hx
  have hy' := (mem_Dst P ρ).mp hy
  have hw : ∀ g : ↥(GK K), ∃ v : V, stRep P ρ g z - z = v ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
    intro g
    refine GlobalTheory.T.exists_eq_tmul_one_of_monodromy_frobenius_filtration l P AI T ι hιC K V (stRep P ρ g z - z) ?_ ?_ ?_
    · rw [map_sub, ← Module.End.mul_apply, monV_stRep, Module.End.mul_apply, hNz, hx', sub_self]
    · have hφz' : phiV P ℚ_[l] V z = z + y := by rw [← hφz]; abel
      rw [map_sub, ← Module.End.mul_apply, phiV_stRep, Module.End.mul_apply, hφz', map_add (f := _), hy']
      abel
    · rw [map_sub, hιst]
      exact Submodule.sub_mem _ (GlobalTheory.T.actVdR_mem_tensorDeRhamFiltration l P K V ρ 0 g _ hFz) hFz
  choose c hc using hw
  have hc' : ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z := fun g => (hc g).symm
  exact ⟨z, c, _root_.GlobalTheory.cocycle_of_st_coboundary l P AI T K V ρ hρ z c hc', hc', hNz⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodPowDvdByBasisAinfStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriod_pow_dvd_by_basis_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → (∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y ↔ ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∃ (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  first | exact @GlobalTheory.BKLim.WHeightSprime.main | exact GlobalTheory.BKLim.WHeightSprime.main | (intros; apply GlobalTheory.BKLim.WHeightSprime.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesEqProdOfParabolicInductionChain
section
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.SerSys

theorem has_prod_of_inInd : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (π : GLRep g) (L : List (GLRep g)), InInd π L → ∀ F, Has S π.2.ρ F → ∃ fs : List (ZMod g)[X], List.Forall₂ (fun (ρ : GLRep g) f => Has S ρ.2.ρ f) L fs ∧ F = fs.prod := by
  intro g _ S π L hL
  induction hL with
  | nil π h0 _ =>
    intro F hF
    refine ⟨[], List.Forall₂.nil, ?_⟩
    obtain ⟨n, r⟩ := π
    simp only at h0
    subst h0
    obtain ⟨v, -, hv⟩ := hF
    have hne : S.e 0 F ≠ 0 := by
      intro h
      apply hv
      simp [h, actK]
    obtain ⟨hm, hd, -⟩ := S.label 0 F hne
    simpa using Polynomial.eq_one_of_monic_natDegree_zero hm hd
  | cons π σ ρ L hπ _ _ hmap ih =>
    intro F hF
    obtain ⟨f, f', hf, hf', rfl⟩ :=
      GlobalTheory.T.seriesIdempotent_mul_of_maps_to_parabolicInduction g S π.1 σ.1 ρ.1 _ π.2.ρ _ _ σ.2.ρ ρ.2.ρ hπ hmap F hF
    obtain ⟨fs, hfs, rfl⟩ := ih f hf
    exact ⟨f' :: fs, List.Forall₂.cons hf' hfs, by simp [mul_comm]⟩

end GlobalTheory.SerSys
end

