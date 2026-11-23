module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsLevelProjLevelProj
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open scoped Topology

namespace GlobalTheory.LBC

section Groups

variable {k k' : Type} [Field k] [Field k'] [Algebra k k']

def galAct (s : k' ≃ₐ[k] k') (n : ℕ) : GL (Fin n) k' →* GL (Fin n) k' :=
  GeneralLinearGroup.map s.toAlgHom.toRingHom

@[simp] theorem galAct_one (n : ℕ) : galAct (1 : k' ≃ₐ[k] k') n = MonoidHom.id _ := by
  ext g i j; rfl

theorem galAct_mul (s t : k' ≃ₐ[k] k') (n : ℕ) : galAct (s * t) n = (galAct s n).comp (galAct t n) := by
  ext g i j; rfl

def incl (k' : Type) [Field k'] [Algebra k k'] (n : ℕ) : GL (Fin n) k →* GL (Fin n) k' :=
  GeneralLinearGroup.map (algebraMap k k')

@[simp] theorem incl_apply {n : ℕ} (γ : GL (Fin n) k) (i j : Fin n) :
    (incl k' n γ : Matrix (Fin n) (Fin n) k') i j = algebraMap k k' ((γ : Matrix (Fin n) (Fin n) k) i j) := rfl

@[simp] theorem galAct_incl (s : k' ≃ₐ[k] k') {n : ℕ} (γ : GL (Fin n) k) : galAct s n (incl k' n γ) = incl k' n γ := by
  ext i j
  change s (algebraMap k k' ((γ : Matrix (Fin n) (Fin n) k) i j)) = _
  exact s.commutes _


variable (k) in
def norm (s : k' ≃ₐ[k] k') {n : ℕ} (g : GL (Fin n) k') : GL (Fin n) k' :=
  (List.ofFn fun j : Fin (Module.finrank k k') => galAct (s ^ (j : ℕ)) n g).prod

def IsStable (s : k' ≃ₐ[k] k') {n : ℕ} (K : Subgroup (GL (Fin n) k')) : Prop := K.map (galAct s n) = K

end Groups

section Traces

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def IsLevelProj (π : Representation ℂ G V) (K : Subgroup G) (A : V →ₗ[ℂ] V)
    (T : fixed π K →ₗ[ℂ] fixed π K) : Prop :=
  ∀ v : fixed π K, ((T v : V) - A v) ∈ twKer π K 1

def HasLevelTrace (π : Representation ℂ G V) (K : Subgroup G) (A : V →ₗ[ℂ] V) (c : ℂ) : Prop :=
  FiniteDimensional ℂ (fixed π K) ∧ ∃ T, IsLevelProj π K A T ∧ LinearMap.trace ℂ _ T = c

end Traces

section Unique

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V} {K : Subgroup G}
  {A : V →ₗ[ℂ] V}

def levelProj (hc : IsCompl (fixed π K) (twKer π K 1)) (A : V →ₗ[ℂ] V) : fixed π K →ₗ[ℂ] fixed π K :=
  Submodule.projectionOnto _ _ hc ∘ₗ A ∘ₗ (fixed π K).subtype

end Unique

section Lift

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k']
  {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]


variable (k) in
def IsTwInt (s : k' ≃ₐ[k] k') (P : Representation ℂ (GL (Fin n) k') W) (I : W →ₗ[ℂ] W) : Prop :=
  (∀ g, P (galAct s n g) ∘ₗ I = I ∘ₗ P g) ∧ 0 < Module.finrank k k' ∧ I ^ Module.finrank k k' = 1

theorem IsTwInt.mem_fixed {s : k' ≃ₐ[k] k'} {P : Representation ℂ (GL (Fin n) k') W} {I : W →ₗ[ℂ] W}
    (hI : IsTwInt k s P I) {K : Subgroup (GL (Fin n) k')} (hK : IsStable s K) {v : W} (hv : v ∈ fixed P K) :
    I v ∈ fixed P K := by
  intro x
  have hx : (x : GL (Fin n) k') ∈ K.map (galAct s n) := by rw [hK]; exact x.2
  obtain ⟨y, hy, e⟩ := Subgroup.mem_map.1 hx
  have h1 := LinearMap.congr_fun (hI.1 y) v
  simp only [LinearMap.comp_apply] at h1
  have h2 : P y v = v := by simpa using hv ⟨y, hy⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  rw [← e, h1, h2]


variable (k) in
def TwCharVal (s : k' ≃ₐ[k] k') (P : Representation ℂ (GL (Fin n) k') W) (I : W →ₗ[ℂ] W) (g' : GL (Fin n) k')
    (c : ℂ) : Prop :=
  ∃ U ∈ 𝓝 (1 : GL (Fin n) k'), ∀ K : Subgroup (GL (Fin n) k'), IsOpen (K : Set (GL (Fin n) k')) →
    IsCompact (K : Set (GL (Fin n) k')) → IsStable s K → (K : Set (GL (Fin n) k')) ⊆ U →
      HasLevelTrace P K (P g' ∘ₗ I) c

def CharVal (π : Representation ℂ (GL (Fin n) k) V) (γ : GL (Fin n) k) (c : ℂ) : Prop :=
  ∃ U ∈ 𝓝 (1 : GL (Fin n) k), ∀ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) →
    IsCompact (K : Set (GL (Fin n) k)) → (K : Set (GL (Fin n) k)) ⊆ U → HasLevelTrace π K (π γ) c

def IsLBC (s : k' ≃ₐ[k] k') (π : Representation ℂ (GL (Fin n) k) V) (P : Representation ℂ (GL (Fin n) k') W) :
    Prop :=
  IsSmooth π ∧ π.IsIrreducible ∧ IsSmooth P ∧ P.IsIrreducible ∧
  ∃ I : W →ₗ[ℂ] W, IsTwInt k s P I ∧
    ∀ g' : GL (Fin n) k', (norm k s g' : Matrix (Fin n) (Fin n) k').charpoly.Separable →
      ∀ γ : GL (Fin n) k, (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k k') =
          (norm k s g' : Matrix (Fin n) (Fin n) k').charpoly →
        ∃ c : ℂ, TwCharVal k s P I g' c ∧ CharVal π γ c

def IsLBCCl (s : k' ≃ₐ[k] k') (x : IrrGL (k := k)) (y : IrrGL (k := k')) : Prop :=
  ∃ (m : ℕ) (π : IrrRep (GL (Fin m) k)) (P : IrrRep (GL (Fin m) k')), x = ⟨m, π.cl⟩ ∧ y = ⟨m, P.cl⟩ ∧
    IsLBC s π.ρ P.ρ

end Lift

end GlobalTheory.LBC
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivProdIrrZero
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open GlobalTheory.Parabolic (Embeds isIrreducible_of_equiv mem_fixed)

namespace GlobalTheory.LocGL.Tests

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem nonempty_equiv_parInd_zero {d : Fin 0 → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin 0)
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) V) (L : ℂ ≃ₗ[ℂ] V) :
    Nonempty ((detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (parInd e ρ)) := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  let f : ℂ →ₗ[ℂ] IndSp e ρ :=
    { toFun := fun c => ⟨⟨fun _ => L c, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (hg _)
          simp⟩, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun g => rfl)⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_add L a b))
      map_smul' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_smul L a b)) }
  refine ⟨equivOfBijective ⟨f, fun g => by rw [hg g, map_one, map_one]; rfl⟩ ⟨fun a b h => ?_, fun φ => ?_⟩⟩
  · have h1 : L a = L b := congrArg (fun φ : IndSp e ρ => φ.1.1 1) h
    exact L.injective h1
  · refine ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun g => ?_))⟩
    rw [hg g]
    exact L.apply_symm_apply _

theorem nonempty_equiv_prodIrr_zero (x : Fin 0 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = 0) :
    Nonempty ((detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (prodIrr x hd)) :=
  nonempty_equiv_parInd_zero _ _ (PiTensorProduct.isEmptyEquiv (R := ℂ) (Fin 0) (s := fun a => (x a).2.rep.V)).symm

theorem empty_spec : IsZ (0 : Multiset (Segment k)) (detRep (Fin 0) (1 : kˣ →* ℂˣ)) ∧
    IsL (0 : Multiset (Segment k)) (detRep (Fin 0) (1 : kˣ →* ℂˣ)) := by
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_zero (k := k) Fin.elim0 rfl
  have ho : IsOrderedForm (k := k) (Fin.elim0 : Fin 0 → Segment k) 0 := ⟨rfl, fun i => i.elim0⟩
  exact ⟨⟨0, Fin.elim0, rfl, ⟨_, ho, fun i => i.elim0⟩, (isSocle_self (isIrreducible_ofChar _)).of_equiv (.refl _) φ⟩,
    ⟨0, Fin.elim0, rfl, ⟨_, ho, fun i => i.elim0⟩, (isCosocle_self (isIrreducible_ofChar _)).of_equiv (.refl _) φ⟩⟩

end GlobalTheory.LocGL.Tests
end
end

