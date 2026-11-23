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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedParabolicInductionReindexEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SmGL.Relabel

section General

variable {F G H V : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]

def indPull {P : Subgroup G} {Q : Subgroup H}
    {σ : Representation F P V} {τ : Representation F Q V} (φ : H →* G) (hφ : Continuous φ)
    (h : ∀ q : Q, ∃ p : P, (p : G) = φ q ∧ σ p = τ q) :
    smoothPart (ind P σ) →ₗ[F] smoothPart (ind Q τ) where
  toFun f := ⟨⟨fun g => f.1.1 (φ g), fun q g => by
      obtain ⟨p, hp, hs⟩ := h q
      show f.1.1 (φ (q * g)) = τ q (f.1.1 (φ g))
      rw [map_mul, ← hp, f.1.2 p, hs]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      (IsOpen.mem_nhds (IsOpen.preimage hφ f.2) (by simp)) fun g hg => by
        have hg' : ind P σ (φ g) f.1 = f.1 := hg
        apply Subtype.ext
        funext x
        have := congrFun (congrArg Subtype.val hg') (φ x)
        show f.1.1 (φ (x * g)) = f.1.1 (φ x)
        rw [map_mul]
        exact this)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem smInd_equiv_comp {P : Subgroup G} {Q : Subgroup H}
    {σ : Representation F P V} {τ : Representation F Q V} (φ : G →* H) (φ' : H →* G)
    (hφ : Continuous φ) (hφ' : Continuous φ') (h1 : ∀ x, φ (φ' x) = x) (h2 : ∀ x, φ' (φ x) = x)
    (h : ∀ q : Q, ∃ p : P, (p : G) = φ' q ∧ σ p = τ q)
    (h' : ∀ p : P, ∃ q : Q, (q : H) = φ p ∧ τ q = σ p) :
    Nonempty ((smInd P σ).Equiv ((smInd Q τ).comp φ)) := by
  refine ⟨.mk (LinearEquiv.ofLinear (indPull φ' hφ' h) (indPull φ hφ h') ?_ ?_) fun g => ?_⟩
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (φ (φ' x)) = f.1.1 x
    rw [h1]
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (φ' (φ x)) = f.1.1 x
    rw [h2]
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (φ' x * g) = f.1.1 (φ' (x * φ g))
    rw [map_mul, h2]

end General

section Blocks

open GlobalTheory.EmptyFirstBlock

variable {R : Type} [CommRing R] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem continuous_reindexGL [TopologicalSpace R] (ψ : n ≃ n') :
    Continuous (reindexGL (R := R) ψ) :=
  Continuous.units_map _ (continuous_pi fun i => continuous_pi fun j =>
    continuous_apply_apply (ψ.symm i) (ψ.symm j))

theorem reindexGL_symm_reindexGL (ψ : n ≃ n') (g : GL n R) :
    reindexGL ψ.symm (reindexGL ψ g) = g :=
  Units.ext (Matrix.ext fun i j => by simp [val_reindexGL])

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

theorem exists_parab_reindexGL {e : (Σ a, m a) ≃ n} {e' : (Σ a, m a) ≃ n'} (ψ : n ≃ n')
    (h : ∀ x, ψ.symm (e' x) = e x) (p : parab R e) :
    ∃ q : parab R e', (q : GL n' R) = reindexGL ψ p ∧ leviProj R e' q = leviProj R e p := by
  refine ⟨⟨reindexGL ψ p, mem_parab_iff.2 fun a b i j hab => ?_⟩, rfl, ?_⟩
  · rw [val_reindexGL, h, h]
    exact mem_parab_iff.1 p.2 a b i j hab
  · funext a
    ext i j
    show (reindexGL ψ (p : GL n R) : Matrix n' n' R) (e' ⟨a, i⟩) (e' ⟨a, j⟩) =
      ((p : GL n R) : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩)
    rw [val_reindexGL, h, h]

end Blocks

theorem parInd_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (e : (Σ a, m a) ≃ n) (ψ : n ≃ n')
    (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W),
    Nonempty ((parInd e ρ).Equiv ((parInd (e.trans ψ) ρ).comp (GlobalTheory.EmptyFirstBlock.reindexGL (R := k) ψ))) := by
  intro k _ _ _ _ α _ _ m _ _ n n' _ _ _ _ e ψ W _ _ ρ
  refine smInd_equiv_comp _ (GlobalTheory.EmptyFirstBlock.reindexGL (R := k) ψ.symm)
    (continuous_reindexGL ψ) (continuous_reindexGL ψ.symm)
    (reindexGL_symm_reindexGL ψ.symm) (reindexGL_symm_reindexGL ψ) (fun q => ?_) (fun p => ?_)
  · obtain ⟨p, hp, hl⟩ := exists_parab_reindexGL (e' := e) ψ.symm (fun x => rfl) q
    exact ⟨p, hp, congrArg (twist ρ (deltaHalf k m)) hl⟩
  · obtain ⟨q, hq, hl⟩ := exists_parab_reindexGL (e' := e.trans ψ) ψ (fun x => by simp) p
    exact ⟨q, hq, congrArg (twist ρ (deltaHalf k m)) hl⟩

end GlobalTheory.SmGL.Relabel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeft
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ProdReorder
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.ProdReorder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ind₂_line_left {r : ℕ} (h : 0 + r = r) {M V : Type} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin 0) k) M) (κ : M ≃ₗ[ℂ] ℂ)
    (π : Representation ℂ (GL (Fin r) k) V) (hπ : IsSmooth π) :
    Nonempty ((ind₂ (stdSum h) (extTensor σ π)).Equiv π) := by
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  have hE : ∀ g w, σ g w = w := fun g w => by rw [Subsingleton.elim g 1, map_one]; rfl
  let L : V ≃ₗ[ℂ] M ⊗[ℂ] V :=
    (TensorProduct.lid ℂ V).symm ≪≫ₗ TensorProduct.congr κ.symm (LinearEquiv.refl ℂ V)
  let u := κ.symm 1
  have hL : ∀ v, L v = u ⊗ₜ[ℂ] v := fun v => by simp [L, u]
  have hs : ∀ i : Fin r, stdSum h (Sum.inr i) = i := fun i => Fin.ext (by simp)
  have hl : ∀ p : parab k (two (stdSum h)), (leviProj k (two (stdSum h)) p true : GL (Fin r) k) = p :=
    fun p => by
      ext i j
      rw [leviProj_apply, two_true, two_true, hs, hs]
  have hd : ∀ p : parab k (two (stdSum h)),
      deltaHalf k (Two (Fin 0) (Fin r)) (leviProj k (two (stdSum h)) p) = 1 := fun p => by
    have : leviProj k (two (stdSum h)) p =
        leviTwo k _ _ ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k (two (stdSum h)) p)) :=
      ((leviTwo k _ _).apply_symm_apply _).symm
    rw [this, deltaHalf_two,
      Subsingleton.elim ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k (two (stdSum h)) p)).1 1]
    simp
  have hP : ∀ g : GL (Fin r) k, g ∈ parab k (two (stdSum h)) := fun g =>
    (mem_parab_two k).2 fun j i => i.elim0
  have law : ∀ (p : parab k (two (stdSum h))) v,
      (deltaHalf k (Two (Fin 0) (Fin r)) (leviProj k (two (stdSum h)) p) : ℂ) •
        (extTensor σ π) ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k (two (stdSum h)) p)) (L v) =
          L (π p v) := fun p v => by
    rw [hd, Units.val_one, one_smul, hL, hL, extTensor_tmul, hE]
    congr 1
    exact congrArg (fun g => π g v) (hl p)
  let f : π.IntertwiningMap (ind₂ (stdSum h) (extTensor σ π)) :=
    { toFun := fun v => ⟨⟨fun x => L (π x v), fun p x => by
          show L (π (↑p * x) v) = (deltaHalf k _ (leviProj k _ p) : ℂ) •
            (extTensor σ π) ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k _ p)) (L (π x v))
          rw [law, map_mul, Module.End.mul_apply]⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg => by
          have hg' : π g v = v := hg
          refine Subtype.ext (funext fun x => ?_)
          show L (π (x * g) v) = L (π x v)
          rw [map_mul, Module.End.mul_apply, hg'])⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x (v + w)) = L (π x v) + L (π x w)
        rw [map_add (f := _), map_add (f := _)]))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x ((c : ℂ) • v)) = (c : ℂ) • L (π x v)
        rw [map_smul, map_smul]))
      isIntertwining' := fun g => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x (π g v)) = L (π (x * g) v)
        rw [map_mul, Module.End.mul_apply])) }
  have hb : Function.Bijective f := by
    refine ⟨fun v w hvw => ?_, fun φ => ⟨L.symm (φ.1.1 1), ?_⟩⟩
    · have h1 : L (π 1 v) = L (π 1 w) := congrArg (fun φ => φ.1.1 1) hvw
      rw [map_one, Module.End.one_apply, Module.End.one_apply] at h1
      exact L.injective h1
    · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
      have h1 := φ.1.2 ⟨x, hP x⟩ 1
      rw [mul_one] at h1
      refine (law ⟨x, hP x⟩ _).symm.trans ?_
      rw [L.apply_symm_apply]
      exact h1.symm
  exact ⟨(GlobalTheory.LocGL.equivOfBijective f hb).symm⟩


variable (k) in
theorem ind₂_unit_left (r t : ℕ) (h : t + r = r) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin r) k) V) (hπ : IsSmooth π) (d : Fin 0 → ℕ) (X : Fin 0 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (e : (Σ a, Fin (d a)) ≃ Fin t) :
    Nonempty ((ind₂ (stdSum h) (extTensor (multiProd e τ) π)).Equiv π) := by
  have ht : t = 0 := by omega
  subst ht
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  let ev1 : IndSp e (piTensor τ) →ₗ[ℂ] ⨂[ℂ] i, X i :=
    { toFun := fun f => f.1.1 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let κ : IndSp e (piTensor τ) ≃ₗ[ℂ] ℂ := (LinearEquiv.ofBijective ev1 ⟨fun f g hfg =>
    Subtype.ext (Subtype.ext (funext fun x => by rw [Subsingleton.elim x 1]; exact hfg)), fun v =>
    ⟨⟨⟨fun _ => v, fun p _ => by rw [Subsingleton.elim p 1, map_one]; rfl⟩,
      GlobalTheory.SmGL.MultiIrr.mem_smooth_of_eventually _ (.of_forall fun _ _ => rfl)⟩, rfl⟩⟩).trans
    (PiTensorProduct.isEmptyEquiv _)
  exact ind₂_line_left h (multiProd e τ) κ π hπ

end GlobalTheory.ProdReorder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PotSemistableParameterBlockSumEqDirectSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.Pst.SumOneField

open Module TensorProduct GlobalTheory.Pst.DpstMap

section FrobSS

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem isFrobSS_sum {ρ₁ : Weil h → End ℂ V} {N₁ : End ℂ V} {a : WDRep h V}
    {ρ₂ : Weil h → End ℂ V'} {N₂ : End ℂ V'} {b : WDRep h V'}
    (ha : IsFrobSS ρ₁ N₁ a) (hb : IsFrobSS ρ₂ N₂ b) :
    IsFrobSS (fun g => (ρ₁ g).prodMap (ρ₂ g)) (N₁.prodMap N₂) (a.sum b) := by
  refine ⟨by rw [WDRep.sum_N, ha.1, hb.1], fun g => ?_⟩
  obtain ⟨c1, n1⟩ := ha.2 g
  obtain ⟨c2, n2⟩ := hb.2 g
  let R := LinearMap.prodMapRingHom ℂ V V'
  have e1 : (a.sum b).ρ g = R (a.ρ g, b.ρ g) := rfl
  have e2 : (ρ₁ g).prodMap (ρ₂ g) = R (ρ₁ g, ρ₂ g) := rfl
  show Commute ((a.sum b).ρ g) ((ρ₁ g).prodMap (ρ₂ g)) ∧ IsNilpotent ((ρ₁ g).prodMap (ρ₂ g) - (a.sum b).ρ g)
  rw [e1, e2]
  have hc : Commute ((a.ρ g, b.ρ g) : End ℂ V × End ℂ V') (ρ₁ g, ρ₂ g) := Prod.ext c1.eq c2.eq
  refine ⟨hc.map R, ?_⟩
  rw [← map_sub]
  obtain ⟨m, hm⟩ := n1
  obtain ⟨n, hn⟩ := n2
  refine IsNilpotent.map ⟨m + n, Prod.ext ?_ ?_⟩ R
  · simp [pow_add, hm]
  · simp [pow_add, hn]

end FrobSS

section Tens

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V V' V'' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
  [AddCommGroup V''] [Module LL V''] [Module ℚ_[l] V''] [IsScalarTower ℚ_[l] LL V'']

theorem tensV_comp (f : V →ₗ[LL] V') (g : V' →ₗ[LL] V'') (z : V ⊗[ℚ_[l]] Bst P) :
    tensV P g (tensV P f z) = tensV P (g ∘ₗ f) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tensV_id (z : V ⊗[ℚ_[l]] Bst P) : tensV P (LinearMap.id : V →ₗ[LL] V) z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tensV_zero (z : V ⊗[ℚ_[l]] Bst P) : tensV P (0 : V →ₗ[LL] V') z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    change ((0 : V →ₗ[LL] V') v) ⊗ₜ[ℚ_[l]] b = 0
    simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]

theorem tensV_add (f g : V →ₗ[LL] V') (z : V ⊗[ℚ_[l]] Bst P) :
    tensV P (f + g) z = tensV P f z + tensV P g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    change (f + g) v ⊗ₜ[ℚ_[l]] b = f v ⊗ₜ[ℚ_[l]] b + g v ⊗ₜ[ℚ_[l]] b
    simp [add_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; abel

end Tens

section Split

variable (k : Type) [Field k] (a b : ℕ)

def pr₁ : (Fin (a + b) → k) →ₗ[k] (Fin a → k) :=
  LinearMap.fst k _ _ ∘ₗ (GlobalTheory.DirectSumLocal.splitEquiv k a b).toLinearMap

def pr₂ : (Fin (a + b) → k) →ₗ[k] (Fin b → k) :=
  LinearMap.snd k _ _ ∘ₗ (GlobalTheory.DirectSumLocal.splitEquiv k a b).toLinearMap

def in₁ : (Fin a → k) →ₗ[k] (Fin (a + b) → k) :=
  (GlobalTheory.DirectSumLocal.splitEquiv k a b).symm.toLinearMap ∘ₗ LinearMap.inl k _ _

def in₂ : (Fin b → k) →ₗ[k] (Fin (a + b) → k) :=
  (GlobalTheory.DirectSumLocal.splitEquiv k a b).symm.toLinearMap ∘ₗ LinearMap.inr k _ _

theorem pr₁_in₁ : pr₁ k a b ∘ₗ in₁ k a b = LinearMap.id := by ext v <;> simp [pr₁, in₁]
theorem pr₂_in₁ : pr₂ k a b ∘ₗ in₁ k a b = 0 := by ext v <;> simp [pr₂, in₁]
theorem pr₁_in₂ : pr₁ k a b ∘ₗ in₂ k a b = 0 := by ext v <;> simp [pr₁, in₂]
theorem pr₂_in₂ : pr₂ k a b ∘ₗ in₂ k a b = LinearMap.id := by ext v <;> simp [pr₂, in₂]
theorem in_pr : in₁ k a b ∘ₗ pr₁ k a b + in₂ k a b ∘ₗ pr₂ k a b = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  simp only [pr₁, pr₂, in₁, in₂, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, ← map_add (f := _)]
  apply (GlobalTheory.DirectSumLocal.splitEquiv k a b).injective
  simp

end Split

end GlobalTheory.Pst.SumOneField

namespace GlobalTheory.Pst.SumOneField

open Module TensorProduct GlobalTheory.Pst.DpstMap

section WdLin

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K LL : FinExt l}
  {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁]
  [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂]
  [AddCommGroup V₃] [Module ↥LL.1 V₃] [Module ℚ_[l] V₃] [IsScalarTower ℚ_[l] ↥LL.1 V₃]
  {r₁ : Representation ↥LL.1 ↥(GK K) V₁} {r₂ : Representation ↥LL.1 ↥(GK K) V₂}
  {r₃ : Representation ↥LL.1 ↥(GK K) V₃}

theorem wdLin_comp_eq_id {f : V₁ →ₗ[↥LL.1] V₂} {g : V₂ →ₗ[↥LL.1] V₁} (hf : ∀ x v, f (r₁ x v) = r₂ x (f v))
    (hg : ∀ x v, g (r₂ x v) = r₁ x (g v)) (hgf : g ∘ₗ f = LinearMap.id) :
    wdLin P ι hg ∘ₗ wdLin P ι hf = LinearMap.id :=
  LinearMap.ext_on_range (span_wdMk P ι r₁) fun x => congrArg (wdMk P ι r₁) (Subtype.ext
    ((tensV_comp P f g x.1).trans ((congrArg (fun k => tensV P k x.1) hgf).trans (tensV_id P x.1))))

theorem wdLin_comp_eq_zero {f : V₁ →ₗ[↥LL.1] V₂} {g : V₂ →ₗ[↥LL.1] V₃} (hf : ∀ x v, f (r₁ x v) = r₂ x (f v))
    (hg : ∀ x v, g (r₂ x v) = r₃ x (g v)) (hgf : g ∘ₗ f = 0) :
    wdLin P ι hg ∘ₗ wdLin P ι hf = 0 :=
  LinearMap.ext_on_range (span_wdMk P ι r₁) fun x => (congrArg (wdMk P ι r₃) (Subtype.ext
    ((tensV_comp P f g x.1).trans ((congrArg (fun k => tensV P k x.1) hgf).trans (tensV_zero P x.1))))).trans
      (wdMk_zero P ι r₃)

end WdLin

section Iso

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)

theorem isFrobSS_wdRep {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] (r : Representation ↥LL.1 ↥(GK Bw.Kw) V)
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P r)] :
    IsFrobSS (wdRho P ι Bw h hj r) (wdN P ι r) (wdRep P ι Bw h hj r) := by
  obtain ⟨u, hN, hu, -, hc, hr⟩ := wdRep_spec P ι Bw h hj r
  rw [← hN]
  exact isFrobSS_of_unipotent u hu hc hr

variable {LL : FinExt l} {a b : ℕ} (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) (Fin (a + b) → ↥LL.1))
  (ρ₁ : Representation ↥LL.1 ↥(GK Bw.Kw) (Fin a → ↥LL.1)) (ρ₂ : Representation ↥LL.1 ↥(GK Bw.Kw) (Fin b → ↥LL.1))
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₁)]
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₂)]

theorem wdRep_iso_sum
    (he : ∀ g v, GlobalTheory.DirectSumLocal.splitEquiv (↥LL.1) a b (ρ g v) =
      (ρ₁ g (GlobalTheory.DirectSumLocal.splitEquiv (↥LL.1) a b v).1, ρ₂ g (GlobalTheory.DirectSumLocal.splitEquiv (↥LL.1) a b v).2)) :
    (wdRep P ι Bw h hj ρ).Iso ((wdRep P ι Bw h hj ρ₁).sum (wdRep P ι Bw h hj ρ₂)) := by
  have hp₁ : ∀ g v, pr₁ (↥LL.1) a b (ρ g v) = ρ₁ g (pr₁ (↥LL.1) a b v) := fun g v => by
    simp only [pr₁, LinearMap.comp_apply, LinearEquiv.coe_coe, he, LinearMap.fst_apply]
  have hp₂ : ∀ g v, pr₂ (↥LL.1) a b (ρ g v) = ρ₂ g (pr₂ (↥LL.1) a b v) := fun g v => by
    simp only [pr₂, LinearMap.comp_apply, LinearEquiv.coe_coe, he, LinearMap.snd_apply]
  have hi₁ : ∀ g v, in₁ (↥LL.1) a b (ρ₁ g v) = ρ g (in₁ (↥LL.1) a b v) := fun g v => by
    apply (GlobalTheory.DirectSumLocal.splitEquiv (↥LL.1) a b).injective
    rw [he]; simp [in₁]
  have hi₂ : ∀ g v, in₂ (↥LL.1) a b (ρ₂ g v) = ρ g (in₂ (↥LL.1) a b v) := fun g v => by
    apply (GlobalTheory.DirectSumLocal.splitEquiv (↥LL.1) a b).injective
    rw [he]; simp [in₂]
  let Φ : WDSpace P ι ρ →ₗ[ℂ] WDSpace P ι ρ₁ × WDSpace P ι ρ₂ := (wdLin P ι hp₁).prod (wdLin P ι hp₂)
  let Ψ : WDSpace P ι ρ₁ × WDSpace P ι ρ₂ →ₗ[ℂ] WDSpace P ι ρ := (wdLin P ι hi₁).coprod (wdLin P ι hi₂)
  have hΨΦ : Ψ ∘ₗ Φ = LinearMap.id := LinearMap.ext_on_range (span_wdMk P ι ρ) fun x => by
    show wdLin P ι hi₁ (wdLin P ι hp₁ (wdMk P ι ρ x)) + wdLin P ι hi₂ (wdLin P ι hp₂ (wdMk P ι ρ x)) = wdMk P ι ρ x
    exact (wdMk_add P ι ρ _ _).symm.trans (congrArg (wdMk P ι ρ) (Subtype.ext
      ((Submodule.coe_add _ _).trans ((congrArg₂ (· + ·) (tensV_comp P (pr₁ (↥LL.1) a b) (in₁ (↥LL.1) a b) x.1)
      (tensV_comp P (pr₂ (↥LL.1) a b) (in₂ (↥LL.1) a b) x.1)).trans ((tensV_add P _ _ x.1).symm.trans
        ((congrArg (fun f => tensV P f x.1) (in_pr (↥LL.1) a b)).trans (tensV_id P x.1)))))))
  have c11 := wdLin_comp_eq_id P ι hi₁ hp₁ (pr₁_in₁ (↥LL.1) a b)
  have c22 := wdLin_comp_eq_id P ι hi₂ hp₂ (pr₂_in₂ (↥LL.1) a b)
  have c21 := wdLin_comp_eq_zero P ι hi₁ hp₂ (pr₂_in₁ (↥LL.1) a b)
  have c12 := wdLin_comp_eq_zero P ι hi₂ hp₁ (pr₁_in₂ (↥LL.1) a b)
  have hΦΨ : Φ ∘ₗ Ψ = LinearMap.id := LinearMap.ext fun y => Prod.ext
    (show wdLin P ι hp₁ (wdLin P ι hi₁ y.1 + wdLin P ι hi₂ y.2) = y.1 from
      ((LinearMap.map_add (wdLin P ι hp₁) _ _).trans (congrArg₂ (· + ·) (LinearMap.congr_fun c11 y.1)
        (LinearMap.congr_fun c12 y.2))).trans (add_zero y.1))
    (show wdLin P ι hp₂ (wdLin P ι hi₁ y.1 + wdLin P ι hi₂ y.2) = y.2 from
      ((LinearMap.map_add (wdLin P ι hp₂) _ _).trans (congrArg₂ (· + ·) (LinearMap.congr_fun c21 y.1)
        (LinearMap.congr_fun c22 y.2))).trans (zero_add y.2))
  let e : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι ρ₁ × WDSpace P ι ρ₂ := LinearEquiv.ofLinear Φ Ψ hΦΨ hΨΦ
  have hρe : ∀ σ y, e (wdRho P ι Bw h hj ρ σ y) =
      ((wdRho P ι Bw h hj ρ₁ σ).prodMap (wdRho P ι Bw h hj ρ₂ σ)) (e y) := fun σ y =>
    Prod.ext (wdLin_wdRho P ι Bw h hj hp₁ σ y) (wdLin_wdRho P ι Bw h hj hp₂ σ y)
  have hNe : ∀ y, e (wdN P ι ρ y) = ((wdN P ι ρ₁).prodMap (wdN P ι ρ₂)) (e y) := fun y =>
    Prod.ext (wdLin_wdN P ι hp₁ y) (wdLin_wdN P ι hp₂ y)
  have h0 := isFrobSS_wdRep P ι Bw h hj ρ
  have h12 := isFrobSS_sum (isFrobSS_wdRep P ι Bw h hj ρ₁) (isFrobSS_wdRep P ι Bw h hj ρ₂)
  exact IsFrobSS.iso h0 h12 e hρe hNe

end Iso

theorem wdPst_sumRep : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a b : ℕ} (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (s' : ↥(Dec (F := E) A) →* GL (Fin b) ↥L.1), IsPst P (Bw.repE L s) → IsPst P (Bw.repE L s') → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) → wdPst P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) = (wdPst P ι Bw h hj (Bw.repE L s)).lpSum (wdPst P ι Bw h hj (Bw.repE L s')) := by
  intro l _ P ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj L a b s s' hV₁ hV₂ hV
  haveI := hV₁.finite
  haveI := hV₂.finite
  haveI := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, wdPst_of_isPst ι Bw h hj hV₁, wdPst_of_isPst ι Bw h hj hV₂, WD.lpSum_mk]
  exact WD.sound (wdRep_iso_sum P ι Bw h hj _ _ _ fun g v => GlobalTheory.DirectSumLocal.splitEquiv_sumRep s s' _ v)

end GlobalTheory.Pst.SumOneField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepTwistDetAwayFromLStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.TwistAway in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneParamOfLadicRep_twist_det_awayFrom_l : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (a : ℕ) (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : G E Ω →* GL (Fin 1) (Qbar l)), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → Continuous (fun g => ((χ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l))) → GlobalTheory.WeilDeligne.wdOf (h := h) hl ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) = (GlobalTheory.WeilDeligne.wdOf (h := h) hl ι ρ).lpChar (GlobalTheory.WeilDeligne.wdOf (h := h) hl ι χ) := by
  intro E Ω _ _ _ _ _ A w h l _ hl ι a ρ χ hρ hχ
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hρ
  obtain ⟨Nχ, hNχ⟩ := exists_isMonodromy h hl ht hχ
  have hχ0 := isMonodromy_zero_of_line hNχ
  have hN' := isMonodromy_twGL hN hχ0
  obtain ⟨a₀, ha, ea⟩ := hN.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨b₀, hb, eb⟩ := hχ0.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨d, hd, ed⟩ := hN'.wdOf_spec hl ht (deg_frob (h := h)) ι
  rw [ea, eb, ed, WD.lpChar_mk]
  refine WD.sound (WDRep.Iso.symm ?_)
  rw [map_zero] at hb
  refine (isFrobSS_tensor_line ha hb).iso hd (lineEquiv _) (fun g v => ?_) (fun v => ?_)
  · induction v using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [TensorProduct.map_tmul, lineEquiv_tmul, IsMonodromy.rep_apply, wdMat_twGL,
        wdMat_zero, toEndC_smul, map_smul, LinearMap.smul_apply]
      rw [smul_smul]
      congr 1
      simp [toEndC_apply, Matrix.mulVec, dotProduct, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
end

