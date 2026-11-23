module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
section
noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

def UpT {C : Type} [Zero C] {n : ℕ} (M : Matrix (Fin n) (Fin n) C) : Prop := ∀ i j, j < i → M i j = 0

def bor {K : Type} [CommRing K] {n : ℕ} (g : GL (Fin n) K) : Submodule K (Matrix (Fin n) (Fin n) K) where
  carrier := {X | UpT ((g : Matrix (Fin n) (Fin n) K) * X * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
  add_mem' {X Y} hX hY i j h := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, hX i j h, hY i j h, add_zero]
  zero_mem' i j _ := by simp
  smul_mem' c X hX i j h := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, hX i j h, smul_zero]

def lieT (K : Type) [CommRing K] (n : ℕ) : Matrix (Fin n) (Fin n) K := Matrix.diagonal fun i => ((w n i : ℤ) : K)

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k]

@[ext] structure Box (F : Frame l k) (n : ℕ) (C : Type) [CommRing C] where
  r : F.Γ →* GG (m := n) (R := C)
  nu : ∀ s, (r s).right = F.del s
  g : F.V → GL (Fin n) C
  tri : ∀ v s, UpT ((g v : Matrix (Fin n) (Fin n) C) * (r (F.loc v s)).mat *
    (((g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C))

variable {F : Frame l k} {n : ℕ}

namespace Box

variable {C C' : Type} [CommRing C] [CommRing C']

def map (f : C →+* C') (B : Box F n C) : Box F n C' where
  r := (GG.map f).comp B.r
  nu := B.nu
  g v := GeneralLinearGroup.map f (B.g v)
  tri v s i j h := by
    have e : ((GeneralLinearGroup.map f (B.g v) : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') *
        (((GG.map f).comp B.r) (F.loc v s)).mat *
        (((GeneralLinearGroup.map f (B.g v))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') =
        f.mapMatrix ((B.g v : Matrix (Fin n) (Fin n) C) * (B.r (F.loc v s)).mat *
          (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) := by
      rw [map_mul, map_mul, ← map_inv]
      rfl
    rw [e]
    exact (congrArg f (B.tri v s i j h)).trans (map_zero f)

theorem map_map {C'' : Type} [CommRing C''] (f : C →+* C') (f' : C' →+* C'') (B : Box F n C) :
    (B.map f).map f' = B.map (f'.comp f) := rfl

def Cont (I : Ideal C) (B : Box F n C) : Prop := ∀ i j, AdicCont I fun s => (B.r s).mat i j

structure Of (B : Box F n C) (ρ : NRep F n C) : Prop where
  atc : (B.r F.c).mat = 1
  res : ∀ s : F.G0, (B.r s).mat = ρ.r s
  psi : ∀ v i s, ((B.g v : Matrix (Fin n) (Fin n) C) * ρ.r (F.loc0 v s) *
    (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) i i = ρ.ψ v i s

theorem Of.map {B : Box F n C} {ρ : NRep F n C} (h : B.Of ρ) (f : C →+* C') : (B.map f).Of (ρ.map f) := by
  refine ⟨?_, ?_, ?_⟩
  · show ((B.r F.c).mat).map f = 1
    rw [h.atc]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  · intro s
    show ((B.r s).mat).map f = _
    rw [h.res]
    rfl
  · intro v i s
    have e : (((B.map f).g v : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') * (ρ.map f).r (F.loc0 v s) *
        ((((B.map f).g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') =
        f.mapMatrix ((B.g v : Matrix (Fin n) (Fin n) C) * ρ.r (F.loc0 v s) *
          (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) := by
      rw [map_mul, map_mul]
      rfl
    rw [e]
    exact congrArg f (h.psi v i s)

def ad (B : Box F n C) : Representation C F.Γ (Matrix (Fin n) (Fin n) C) := adRep B.r

def b (B : Box F n C) (v : F.V) : Submodule C (Matrix (Fin n) (Fin n) C) := bor (B.g v)

end Box

structure NRep.Good {K : Type} [Field K] (ρ : NRep F n K) : Prop where
  two : (2 : K) ≠ 0
  zd : ∀ i j, i ≠ j → (ρ.r F.g0 - ρ.r (F.star F.g0)) i i ≠ (ρ.r F.g0 - ρ.r (F.star F.g0)) j j
  ψd : ∀ v, ∃ s, ∀ i j, i ≠ j → ρ.ψ v i s ≠ ρ.ψ v j s

section CO

variable (O : Type) [CommRing O] [IsLocalRing O]

abbrev NRep.bar {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (ρ : NRep F n C) : NRep F n (ResidueField O) :=
  ρ.map (res O C : C →+* ResidueField O)

abbrev Box.bar {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (B : Box F n C) : Box F n (ResidueField O) :=
  B.map (res O C : C →+* ResidueField O)

structure NRep.Univ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) : Prop where
  cont : ρ.Cont (maximalIdeal R)
  univ : ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (ρ' : NRep F n C), ρ'.Cont (maximalIdeal C) →
    ρ'.bar O = ρ.bar O → ∃! g : R →ₐ[O] C, ρ.map (g : R →+* C) = ρ'

abbrev Tan (R : Type) [CommRing R] [Algebra O R] [IsCO O R] : Submodule (ResidueField O) (R →ₗ[O] ResidueField O) :=
  PtDer (res O R) (ResidueField O)

def Box.tanCo {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (B : Box F n R) :
    (R →ₗ[O] ResidueField O) →ₗ[ResidueField O] (F.Γ → Matrix (Fin n) (Fin n) (ResidueField O)) where
  toFun D s := (B.r s).mat.map D *
    ((((B.bar O).r s).left⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))
  map_add' D D' := funext fun s => by
    rw [Pi.add_apply, ← Matrix.add_mul]
    rfl
  map_smul' c D := funext fun s => by
    rw [Pi.smul_apply, RingHom.id_apply, ← Matrix.smul_mul]
    rfl

structure IsSq {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (μ : ResidueField O →+ C) : Prop where
  mul : ∀ a c, μ (res O C a * c) = a * μ c
  mem : ∀ c, μ c ∈ maximalIdeal C

variable {O}


open Classical in
def evK {C : Type} [CommRing C] [Algebra O C] (K : Ideal C) (u : K →ₗ[O] ResidueField O) (x : C) : ResidueField O :=
  if h : x ∈ K then u ⟨x, h⟩ else 0

theorem evK_of_mem {C : Type} [CommRing C] [Algebra O C] {K : Ideal C} (u : K →ₗ[O] ResidueField O) {x : C}
    (h : x ∈ K) : evK K u x = u ⟨x, h⟩ := dite_eq_left h

variable {C' C : Type} [CommRing C'] [Algebra O C'] [IsCO O C'] [CommRing C] [Algebra O C]

structure SetLift (p : C' →ₐ[O] C) (B : Box F n C) where
  r : F.Γ → GL (Fin n) C'
  r_cont : ∀ i j, AdicCont (maximalIdeal C') fun s => r s i j
  r_map : ∀ s, GeneralLinearGroup.map (p : C' →+* C) (r s) = (B.r s).left
  g : F.V → GL (Fin n) C'
  g_map : ∀ v, GeneralLinearGroup.map (p : C' →+* C) (g v) = B.g v
  t : ∀ v, F.Gv v → GL (Fin n) C'
  t_cont : ∀ v i j, AdicCont (maximalIdeal C') fun s => t v s i j
  t_tri : ∀ v s, UpT (t v s : Matrix (Fin n) (Fin n) C')
  t_map : ∀ v s, GeneralLinearGroup.map (p : C' →+* C) (t v s) = B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹

namespace SetLift

variable {p : C' →ₐ[O] C} {B : Box F n C} (D : SetLift p B)

def om (x : F.Γ × F.Γ) : Matrix (Fin n) (Fin n) C' :=
  ((D.r x.1 * sgnAct n C' (F.del x.1) (D.r x.2) * (D.r (x.1 * x.2))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') - 1

def a (v : F.V) (s : F.Gv v) : Matrix (Fin n) (Fin n) C' :=
  ((D.r (F.loc v s) * ((D.g v)⁻¹ * D.t v s * D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') - 1

def co : (RingHom.ker p →ₗ[O] ResidueField O) →ₗ[ResidueField O]
    (F.Γ × F.Γ → Matrix (Fin n) (Fin n) (ResidueField O)) × (∀ v, F.Gv v → Matrix (Fin n) (Fin n) (ResidueField O)) where
  toFun u := (fun x => (D.om x).map (evK _ u), fun v s => (D.a v s).map (evK _ u))
  map_add' u u' := by
    have e : ∀ x, evK _ (u + u') x = evK _ u x + evK _ u' x := fun x => by
      unfold evK
      split_ifs <;> simp
    ext <;> simp [e]
  map_smul' c u := by
    have e : ∀ x, evK _ (c • u) x = c * evK _ u x := fun x => by
      unfold evK
      split_ifs <;> simp
    ext <;> simp [e]

end SetLift


variable (O) in
def HasObs (R : Type) [CommRing R] [Algebra O R] (H : Type) [AddCommGroup H] [Module (ResidueField O) H] : Prop :=
  ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (p : C' →ₐ[O] R), Function.Surjective p →
    maximalIdeal C' * RingHom.ker p = ⊥ →
    ∃ ob : (RingHom.ker p →ₗ[O] ResidueField O) →ₗ[ResidueField O] H, ∀ u, ob u = 0 →
      ∀ (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R),
        p''.comp q = p → Function.Surjective q → (∀ y : RingHom.ker p, u y = 0 → q y = 0) →
        ∃ s : R →ₐ[O] C'', p''.comp s = AlgHom.id O R

def IsMinPres {σ R : Type} [CommRing R] [Algebra O R] (p : MvPowerSeries σ O →ₐ[O] R) : Prop :=
  Function.Surjective p ∧ ∀ f ∈ RingHom.ker p, ∀ s, MvPowerSeries.coeff (Finsupp.single s 1) f ∈ maximalIdeal O

end CO

end UpperTheory.V.Fr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrYMap
section
noncomputable section

namespace UpperTheory.V.Fr.Frame

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (F : Frame l k) (M : Type) [AddCommGroup M] [Module k M]

def strY : Submodule k (F.G0 → M) where
  carrier := {y | IsLocallyConstant y ∧ (∀ g h : F.G0, y (g * h) = (F.Ψ h : k) • y g + y h) ∧
    y F.g0 = y (F.star F.g0) ∧
    (∀ v, ∃ α : M, ∀ s, y (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - 1) • α) ∧
    ∀ v, ∃ β : M, ∀ s, y (F.star (F.loc0 v s)) = (1 - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • β}
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4, a5⟩ ⟨b1, b2, b3, b4, b5⟩
    refine ⟨a1.add b1, fun g h => ?_, by simp [a3, b3], fun v => ?_, fun v => ?_⟩
    · simp only [Pi.add_apply, a2, b2, smul_add]; abel
    · obtain ⟨α, h⟩ := a4 v
      obtain ⟨α', h'⟩ := b4 v
      exact ⟨α + α', fun s => by rw [Pi.add_apply, h, h', smul_add]⟩
    · obtain ⟨α, h⟩ := a5 v
      obtain ⟨α', h'⟩ := b5 v
      exact ⟨α + α', fun s => by rw [Pi.add_apply, h, h', smul_add]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp, rfl, fun _ => ⟨0, by simp⟩, fun _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4, a5⟩
    refine ⟨a1.comp (c • ·), fun g h => ?_, by simp [a3], fun v => ?_, fun v => ?_⟩
    · simp only [Pi.smul_apply, a2, smul_add, smul_comm c]
    · obtain ⟨α, h⟩ := a4 v
      exact ⟨c • α, fun s => by rw [Pi.smul_apply, h, smul_comm]⟩
    · obtain ⟨α, h⟩ := a5 v
      exact ⟨c • α, fun s => by rw [Pi.smul_apply, h, smul_comm]⟩

def strS : Submodule k (F.G0 → M) where
  carrier := {a | IsLocallyConstant a ∧
    (∀ g h : F.G0, a (g * h) = (F.Ψ h : k) • a g + (((F.Ψ g)⁻¹ : kˣ) : k) • a h) ∧ (∀ g, a (F.star g) = a g) ∧
    ∀ v, ∃ γ : M, ∀ s, a (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • γ}
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨a1.add b1, fun g h => ?_, fun g => by simp [a3, b3], fun v => ?_⟩
    · simp only [Pi.add_apply, a2, b2, smul_add]; abel
    · obtain ⟨α, h⟩ := a4 v
      obtain ⟨α', h'⟩ := b4 v
      exact ⟨α + α', fun s => by rw [Pi.add_apply, h, h', smul_add]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp, fun _ => rfl, fun _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4⟩
    refine ⟨a1.comp (c • ·), fun g h => ?_, fun g => by simp [a3], fun v => ?_⟩
    · simp only [Pi.smul_apply, a2, smul_add, smul_comm c]
    · obtain ⟨α, h⟩ := a4 v
      exact ⟨c • α, fun s => by rw [Pi.smul_apply, h, smul_comm]⟩

variable {F M} {M' : Type} [AddCommGroup M'] [Module k M']

theorem strY_map (f : M →ₗ[k] M') {y : F.G0 → M} (hy : y ∈ F.strY M) : (fun g => f (y g)) ∈ F.strY M' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hy
  refine ⟨h1.comp f, fun g h => ?_, congrArg f h3, fun v => ?_, fun v => ?_⟩
  · simp only [h2, map_add (f := _), map_smul]
  · obtain ⟨α, hα⟩ := h4 v
    exact ⟨f α, fun s => by simp only [hα, map_smul]⟩
  · obtain ⟨β, hβ⟩ := h5 v
    exact ⟨f β, fun s => by simp only [hβ, map_smul]⟩

theorem strS_map (f : M →ₗ[k] M') {a : F.G0 → M} (ha : a ∈ F.strS M) : (fun g => f (a g)) ∈ F.strS M' := by
  obtain ⟨h1, h2, h3, h4⟩ := ha
  refine ⟨h1.comp f, fun g h => ?_, fun g => congrArg f (h3 g), fun v => ?_⟩
  · simp only [h2, map_add (f := _), map_smul]
  · obtain ⟨γ, hγ⟩ := h4 v
    exact ⟨f γ, fun s => by simp only [hγ, map_smul]⟩

end UpperTheory.V.Fr.Frame
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TensorProjMemOfMemBaseChange
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {k K : Type} [Field k] [Field K] [Algebra k K]

private theorem rank_eq_of_scalar_extension_data {H H' : Type} [AddCommGroup H] [Module k H] [AddCommGroup H'] [Module K H']
    (ι : H →+ H') (hι : ∀ (a : k) h, ι (a • h) = algebraMap k K a • ι h)
    (π : (K →ₗ[k] k) → H' →+ H) (hπ : ∀ l c h, π l (c • ι h) = l c • h)
    (hs : Submodule.span K (Set.range ι) = ⊤) : Module.rank K H' = Module.rank k H := by
  classical
  let e := Module.Free.chooseBasis k H
  have hli : LinearIndependent K (fun j => ι (e j)) := by
    rw [linearIndependent_iff']
    intro s c hc j hj
    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro l
    have h1 := congrArg (π l) hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h1
    simp only [hπ] at h1
    exact linearIndependent_iff'.1 e.linearIndependent s (fun j => l (c j)) h1 j hj
  have hsp : ⊤ ≤ Submodule.span K (Set.range fun j => ι (e j)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    have hh : h ∈ Submodule.span k (Set.range e) := by rw [e.span_eq]; trivial
    induction hh using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact Submodule.subset_span ⟨j, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [hι]; exact Submodule.smul_mem _ _ hx
  rw [← (Module.Basis.mk hli hsp).mk_eq_rank'', ← e.mk_eq_rank'']

variable {W : Type} [AddCommGroup W] [Module k W]

private noncomputable def n4p (l : K →ₗ[k] k) : K ⊗[k] W →ₗ[k] W :=
  (TensorProduct.lid k W).toLinearMap ∘ₗ l.rTensor W

@[simp] private theorem tensor_proj_tmul (l : K →ₗ[k] k) (c : K) (x : W) : n4p l (c ⊗ₜ[k] x) = l c • x := by
  simp [n4p]

private theorem tensor_proj_smul_one_tmul (l : K →ₗ[k] k) (c : K) (x : W) : n4p l (c • ((1 : K) ⊗ₜ[k] x)) = l c • x := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, tensor_proj_tmul]

private theorem tensor_proj_baseChange_map (l : K →ₗ[k] k) (f : W →ₗ[k] W) (x : K ⊗[k] W) :
    n4p l (f.baseChange K x) = f (n4p l x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c x => simp
  | add x y hx hy => simp [hx, hy]

private theorem tensor_proj_mem_of_mem_baseChange (l : K →ₗ[k] k) (b : Submodule k W) (x : K ⊗[k] W) (hx : x ∈ b.baseChange K) :
    n4p l x ∈ b := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.inductionOn with
  | tmul c x => simpa using b.smul_mem _ x.2
  | add x y hx hy => simpa using add_mem hx hy

private theorem baseChange_eq_sum_coord_basis {I : Type} (e : Module.Basis I k K) (x : K ⊗[k] W) :
    ∃ s : Finset I, ∀ t : Finset I, s ⊆ t → x = ∑ i ∈ t, e i • ((1 : K) ⊗ₜ[k] n4p (e.coord i) x) := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul c x =>
    refine ⟨(e.repr c).support, fun t ht => ?_⟩
    have h1 : c = ∑ i ∈ t, e.repr c i • e i := by
      conv_lhs => rw [← e.linearCombination_repr c, Finsupp.linearCombination_apply]
      exact Finsupp.sum_of_support_subset _ ht _ (fun _ _ => by simp)
    conv_lhs => rw [h1]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tensor_proj_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
    rfl
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    refine ⟨s ∪ s', fun t ht => ?_⟩
    conv_lhs => rw [hs t (Finset.subset_union_left.trans ht), hs' t (Finset.subset_union_right.trans ht)]
    simp [← Finset.sum_add_distrib, TensorProduct.tmul_add]

variable {G V : Type}

variable (K) in
private noncomputable def n4i : ((G → W) × (V → W)) →+ ((G → K ⊗[k] W) × (V → K ⊗[k] W)) where
  toFun y := (fun g => (1 : K) ⊗ₜ y.1 g, fun v => (1 : K) ⊗ₜ y.2 v)
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [TensorProduct.tmul_add]

private noncomputable def n4q (l : K →ₗ[k] k) : ((G → K ⊗[k] W) × (V → K ⊗[k] W)) →+ ((G → W) × (V → W)) where
  toFun y := (fun g => n4p l (y.1 g), fun v => n4p l (y.2 v))
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

private theorem inclusion_smul_algebraMap (a : k) (y : (G → W) × (V → W)) :
    n4i (k := k) K (a • y) = algebraMap k K a • n4i (k := k) K y := by
  ext <;> simp [n4i]

private theorem descend_smul_inclusion (l : K →ₗ[k] k) (c : K) (y : (G → W) × (V → W)) :
    n4q l (c • n4i (k := k) K y) = l c • y := by
  ext <;> simp [n4i, n4q, tensor_proj_smul_one_tmul]

variable [Group G] [TopologicalSpace G] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G)
  (ρ : Representation k G W) (b : V → Submodule k W) (ρ' : Representation K G (K ⊗[k] W))
  (hρ : ∀ g, ρ' g = (ρ g).baseChange K)

include hρ

private theorem inclusion_cocycle_mem_Z1 (y) (hy : y ∈ Z1C loc ρ b) :
    n4i (k := k) K y ∈ Z1C loc ρ' (fun v => (b v).baseChange K) := by
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨h1.comp (fun x => (1 : K) ⊗ₜ[k] x), fun s t => ?_, fun v s => ?_⟩
  · simp [n4i, hρ, h2, TensorProduct.tmul_add]
  · have := Submodule.tmul_mem_baseChange_of_mem (1 : K) (h3 v s)
    simpa [n4i, hρ, TensorProduct.tmul_sub] using this

private theorem descend_cocycle_mem_Z1 (l : K →ₗ[k] k) (y) (hy : y ∈ Z1C loc ρ' (fun v => (b v).baseChange K)) :
    n4q l y ∈ Z1C loc ρ b := by
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨h1.comp (n4p l), fun s t => ?_, fun v s => ?_⟩
  · simp [n4q, hρ, h2, tensor_proj_baseChange_map]
  · have := tensor_proj_mem_of_mem_baseChange l _ _ (h3 v s)
    simpa [n4q, hρ, tensor_proj_baseChange_map] using this

omit [TopologicalSpace G] in
private theorem inclusion_coboundary_mem_B1 (y) (hy : y ∈ continuousCoboundaries1 ρ b) :
    n4i (k := k) K y ∈ continuousCoboundaries1 ρ' (fun v => (b v).baseChange K) := by
  obtain ⟨X, h2, h3⟩ := hy
  refine ⟨1 ⊗ₜ X, fun s => ?_, fun v => ?_⟩
  · simp [n4i, hρ, h2, TensorProduct.tmul_sub]
  · have := Submodule.tmul_mem_baseChange_of_mem (1 : K) (h3 v)
    simpa [n4i, TensorProduct.tmul_sub] using this

omit [TopologicalSpace G] in
private theorem descend_coboundary_mem_B1 (l : K →ₗ[k] k) (y) (hy : y ∈ continuousCoboundaries1 ρ' (fun v => (b v).baseChange K)) :
    n4q l y ∈ continuousCoboundaries1 ρ b := by
  obtain ⟨X, h2, h3⟩ := hy
  refine ⟨n4p l X, fun s => ?_, fun v => ?_⟩
  · simp [n4q, hρ, h2, tensor_proj_baseChange_map]
  · have := tensor_proj_mem_of_mem_baseChange l _ _ (h3 v)
    simpa [n4q] using this

private theorem cocycles_baseChange_eq_span [CompactSpace G] [Finite V] :
    Z1C loc ρ' (fun v => (b v).baseChange K) =
      Submodule.span K (n4i (k := k) K '' (Z1C loc ρ b : Set ((G → W) × (V → W)))) := by
  classical
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
  · let e := Module.Free.chooseBasis k K
    choose s hs using fun x : K ⊗[k] W => baseChange_eq_sum_coord_basis e x
    have hf : (Set.range y.1 ∪ Set.range y.2).Finite := hy.1.range_finite.union (Set.finite_range _)
    have hy' : y = ∑ i ∈ hf.toFinset.biUnion s, e i • n4i (k := k) K (n4q (e.coord i) y) := by
      ext g
      · rw [Prod.fst_sum, Finset.sum_apply]
        exact hs _ _ (Finset.subset_biUnion_of_mem s (by simp))
      · rw [Prod.snd_sum, Finset.sum_apply]
        exact hs _ _ (Finset.subset_biUnion_of_mem s (by simp))
    rw [hy']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, descend_cocycle_mem_Z1 loc ρ b ρ' hρ _ y hy, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩
    exact inclusion_cocycle_mem_Z1 loc ρ b ρ' hρ y hy

private theorem rank_H1_baseChange_eq [CompactSpace G] [Finite V] :
    Module.rank K (H1C loc ρ' fun v => (b v).baseChange K) = Module.rank k (H1C loc ρ b) := by
  let i0 : Z1C loc ρ b →+ Z1C loc ρ' (fun v => (b v).baseChange K) :=
    { toFun := fun y => ⟨n4i (k := k) K y.1, inclusion_cocycle_mem_Z1 loc ρ b ρ' hρ _ y.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  let q0 (l : K →ₗ[k] k) : Z1C loc ρ' (fun v => (b v).baseChange K) →+ Z1C loc ρ b :=
    { toFun := fun y => ⟨n4q l y.1, descend_cocycle_mem_Z1 loc ρ b ρ' hρ l _ y.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  let i1 : H1C loc ρ b →+ H1C loc ρ' (fun v => (b v).baseChange K) :=
    QuotientAddGroup.map (Submodule.toAddSubgroup _) (Submodule.toAddSubgroup _) i0
      (fun y hy => inclusion_coboundary_mem_B1 ρ b ρ' hρ _ hy)
  let q1 (l : K →ₗ[k] k) : H1C loc ρ' (fun v => (b v).baseChange K) →+ H1C loc ρ b :=
    QuotientAddGroup.map (Submodule.toAddSubgroup _) (Submodule.toAddSubgroup _) (q0 l)
      (fun y hy => descend_coboundary_mem_B1 ρ b ρ' hρ l _ hy)
  have hi : ∀ y, i1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk (i0 y) := fun _ => rfl
  have hq : ∀ l y, q1 l (Submodule.Quotient.mk y) = Submodule.Quotient.mk (q0 l y) := fun _ _ => rfl
  refine rank_eq_of_scalar_extension_data i1 (fun a h => ?_) q1 (fun l c h => ?_) ?_
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    rw [← Submodule.Quotient.mk_smul, hi, hi, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (inclusion_smul_algebraMap a y.1)
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    rw [hi, ← Submodule.Quotient.mk_smul, hq, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (descend_smul_inclusion l c y.1)
  · rw [eq_top_iff]
    intro h hT
    clear hT
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    have hy' := hy
    rw [cocycles_baseChange_eq_span loc ρ b ρ' hρ] at hy'
    revert hy
    induction hy' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      intro hy
      exact Submodule.subset_span ⟨Submodule.Quotient.mk ⟨z, hz⟩, rfl⟩
    | zero => intro hy; exact zero_mem _
    | add x y hx' hy' hx hy =>
      intro _
      rw [← cocycles_baseChange_eq_span loc ρ b ρ' hρ] at hx' hy'
      exact add_mem (hx hx') (hy hy')
    | smul a x hx' hx =>
      intro _
      rw [← cocycles_baseChange_eq_span loc ρ b ρ' hρ] at hx'
      exact Submodule.smul_mem _ a (hx hx')

end SlopeTestRemainingChoices

theorem UpperTheory.V.Fr.n4 :
    ∀ {k K G W V : Type} [Field k] [Field K] [Algebra k K] [Group G] [TopologicalSpace G] [CompactSpace G] [AddCommGroup W] [Module k W] [Module.Finite k W] {Gv : V → Type} [∀ v, Group (Gv v)] [Finite V] (loc : ∀ v, Gv v →* G) (ρ : Representation k G W) (b : V → Submodule k W) (ρ' : Representation K G (TensorProduct k K W)), (∀ g, ρ' g = (ρ g).baseChange K) → Z1C loc ρ' (fun v => (b v).baseChange K) = Submodule.span K ((fun y : (G → W) × (V → W) => (fun g => (1 : K) ⊗ₜ y.1 g, fun v => (1 : K) ⊗ₜ y.2 v)) '' (Z1C loc ρ b : Set ((G → W) × (V → W)))) ∧ Module.rank K (H1C loc ρ' fun v => (b v).baseChange K) = Module.rank k (H1C loc ρ b) := by
  intro k K G W V _ _ _ _ _ _ _ _ _ Gv _ _ loc ρ b ρ' hρ
  exact ⟨cocycles_baseChange_eq_span loc ρ b ρ' hρ, rank_H1_baseChange_eq loc ρ b ρ' hρ⟩
end

