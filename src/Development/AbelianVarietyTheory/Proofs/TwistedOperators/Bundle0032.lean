module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousWittExtendByZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerEquivUpperSwap
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory

namespace GlobalTheory.SmGL.SwapBlocks

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem smInd_equiv_of_eq [TopologicalSpace G] [IsTopologicalGroup G] {H H' : Subgroup G} (h : H = H')
    (σ : Representation ℂ H V) (σ' : Representation ℂ H' V)
    (hσ : ∀ g (hg : g ∈ H) (hg' : g ∈ H'), σ ⟨g, hg⟩ = σ' ⟨g, hg'⟩) :
    Nonempty ((smInd H σ).Equiv (smInd H' σ')) := by
  subst h
  obtain rfl : σ = σ' := MonoidHom.ext fun g => hσ g.1 g.2 g.2
  exact ⟨Representation.Equiv.refl _⟩

end General

section Blocks

variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n]

end Blocks

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

end Local

open ValuativeRel MeasureTheory in
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] in
private theorem nonempty_equiv_smInd_of_eq [TopologicalSpace G] [IsTopologicalGroup G]
    {W : Type} [AddCommGroup W] [Module ℂ W] {H H' : Subgroup G} (h : H = H')
    (σ : Representation ℂ H W) (σ' : Representation ℂ H' W)
    (hσ : ∀ (g : G) (hg : g ∈ H) (hg' : g ∈ H'), σ ⟨g, hg⟩ = σ' ⟨g, hg'⟩) :
    Nonempty ((_root_.GlobalTheory.PRep.smInd H σ).Equiv (_root_.GlobalTheory.PRep.smInd H' σ')) := by
  subst h
  obtain rfl : σ = σ' := MonoidHom.ext fun p => hσ p p.2 p.2
  exact ⟨Representation.Equiv.refl _⟩

open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem parabLower_eq_parab_sumComm (e : a ⊕ b ≃ n) :
    _root_.GlobalTheory.SmGL.parabLower R (_root_.GlobalTheory.SmGL.two e) =
      _root_.GlobalTheory.SmGL.parab R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e)) := by
  ext g
  rw [_root_.GlobalTheory.SmGL.mem_parabLower_two, _root_.GlobalTheory.SmGL.mem_parab_two]
  simp

open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem leviProj_sumComm_eq_swap_leviProjLower (e : a ⊕ b ≃ n)
    (p : _root_.GlobalTheory.SmGL.parabLower R (_root_.GlobalTheory.SmGL.two e))
    (hp : (p : GL n R) ∈
      _root_.GlobalTheory.SmGL.parab R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e))) :
    _root_.GlobalTheory.SmGL.leviProj R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e)) ⟨p, hp⟩ =
      _root_.GlobalTheory.SmGL.leviTwo R b a
        ((_root_.GlobalTheory.SmGL.leviTwo R a b).symm
          (_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p)).swap := by
  funext x
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  cases x
  · change _ = ((_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p true : GL b R) :
      Matrix b b R) i j
    rw [_root_.GlobalTheory.SmGL.leviProj_apply, _root_.GlobalTheory.SmGL.leviProjLower_apply]
    rfl
  · change _ = ((_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p false : GL a R) :
      Matrix a a R) i j
    rw [_root_.GlobalTheory.SmGL.leviProj_apply, _root_.GlobalTheory.SmGL.leviProjLower_apply]
    rfl

open ValuativeRel MeasureTheory in
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
private theorem deltaHalf_inv_leviTwo_eq_deltaHalf_swap (g : GL a k × GL b k) :
    (_root_.GlobalTheory.SmGL.deltaHalf k (_root_.GlobalTheory.SmGL.Two a b))⁻¹ (_root_.GlobalTheory.SmGL.leviTwo k a b g) =
      _root_.GlobalTheory.SmGL.deltaHalf k (_root_.GlobalTheory.SmGL.Two b a) (_root_.GlobalTheory.SmGL.leviTwo k b a g.swap) := by
  rw [MonoidHom.inv_apply, _root_.GlobalTheory.SmGL.deltaHalf_two,
    _root_.GlobalTheory.SmGL.deltaHalf_two, neg_div, neg_div, _root_.GlobalTheory.SmGL.absPow_neg,
    _root_.GlobalTheory.SmGL.absPow_neg]
  simp only [Prod.fst_swap, Prod.snd_swap, MonoidHom.inv_apply, mul_inv, inv_inv]
  exact mul_comm _ _

open ValuativeRel MeasureTheory in
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] in
private theorem jacquet_apply_eq_of_eq {M M' : Type} [Group M] [Group M']
    (π : Representation ℂ G V) (N : Subgroup G) (s : M →* G) (s' : M' →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G))
    (hs' : ∀ m, s' m ∈ Subgroup.normalizer (N : Set G)) {x : M} {x' : M'} (h : s x = s' x') :
    _root_.GlobalTheory.PRep.jacquet π N s hs x = _root_.GlobalTheory.PRep.jacquet π N s' hs' x' := by
  unfold _root_.GlobalTheory.PRep.jacquet
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  rw [h]

open ValuativeRel MeasureTheory in
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] in
private theorem nonempty_equiv_twist_jacquet_comp {M M' K : Type} [Group M] [Group M'] [Group K]
    (π : Representation ℂ G V) {N N' : Subgroup G} (hN : N = N') (s : M →* G) (s' : M' →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G))
    (hs' : ∀ m, s' m ∈ Subgroup.normalizer (N' : Set G)) (φ : K →* M) (φ' : K →* M')
    (hφ : ∀ x, s (φ x) = s' (φ' x)) (χ : M →* ℂˣ) (χ' : M' →* ℂˣ)
    (hχ : ∀ x, χ (φ x) = χ' (φ' x)) :
    Nonempty (Representation.Equiv
      ((_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).comp φ)
      ((_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N' s' hs') χ').comp φ')) := by
  subst hN
  have h : (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).comp φ =
      (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s' hs') χ').comp φ' := by
    refine MonoidHom.ext fun x => LinearMap.ext fun v => ?_
    simp only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.twist_apply, hχ,
      jacquet_apply_eq_of_eq π N s s' hs hs' (hφ x)]
  rw [h]
  exact ⟨Representation.Equiv.refl _⟩

open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem unipRadLower_eq_unipRad_sumComm (e : a ⊕ b ≃ n) :
    _root_.GlobalTheory.SmGL.unipRadLower R (_root_.GlobalTheory.SmGL.two e) =
      _root_.GlobalTheory.SmGL.unipRad R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e)) := by
  ext g
  rw [_root_.GlobalTheory.SmGL.mem_unipRadLower, _root_.GlobalTheory.SmGL.mem_unipRad,
    parabLower_eq_parab_sumComm]
  refine and_congr_right fun _ => ?_
  simp only [Bool.forall_bool]
  exact and_comm

open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem leviEmb_leviTwo_apply_eq_fromBlocks (e : a ⊕ b ≃ n) (g : GL a R × GL b R) (u v : a ⊕ b) :
    (_root_.GlobalTheory.SmGL.leviEmb R (_root_.GlobalTheory.SmGL.two e) (_root_.GlobalTheory.SmGL.leviTwo R a b g) :
        Matrix n n R) (e u) (e v) =
      Matrix.fromBlocks (g.1 : Matrix a a R) 0 0 (g.2 : Matrix b b R) u v := by
  rcases u with u | u <;> rcases v with v | v
  · rw [← _root_.GlobalTheory.SmGL.two_false e u, ← _root_.GlobalTheory.SmGL.two_false e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_same]
    rfl
  · rw [← _root_.GlobalTheory.SmGL.two_false e u, ← _root_.GlobalTheory.SmGL.two_true e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_ne _ _ _ (by decide : false ≠ true)]
    rfl
  · rw [← _root_.GlobalTheory.SmGL.two_true e u, ← _root_.GlobalTheory.SmGL.two_false e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_ne _ _ _ (by decide : true ≠ false)]
    rfl
  · rw [← _root_.GlobalTheory.SmGL.two_true e u, ← _root_.GlobalTheory.SmGL.two_true e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_same]
    rfl

open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem leviEmb_leviTwo_eq_leviEmb_sumComm_swap (e : a ⊕ b ≃ n) (g : GL a R × GL b R) :
    _root_.GlobalTheory.SmGL.leviEmb R (_root_.GlobalTheory.SmGL.two e) (_root_.GlobalTheory.SmGL.leviTwo R a b g) =
      _root_.GlobalTheory.SmGL.leviEmb R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e))
        (_root_.GlobalTheory.SmGL.leviTwo R b a g.swap) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  obtain ⟨u, rfl⟩ := e.surjective i
  obtain ⟨v, rfl⟩ := e.surjective j
  have hu : e u = ((Equiv.sumComm b a).trans e) u.swap := by simp
  have hv : e v = ((Equiv.sumComm b a).trans e) v.swap := by simp
  rw [leviEmb_leviTwo_apply_eq_fromBlocks, hu, hv, leviEmb_leviTwo_apply_eq_fromBlocks]
  rcases u with u | u <;> rcases v with v | v <;> rfl


open ValuativeRel MeasureTheory in
theorem _root_.GlobalTheory.SmGL.SwapBlocks.lower_equiv_upper_swap : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V], (∀ ρ : Representation ℂ (GL a k × GL b k) V, Nonempty ((_root_.GlobalTheory.SmGL.ind₂Lower e ρ).Equiv (_root_.GlobalTheory.SmGL.ind₂ ((Equiv.sumComm b a).trans e) (ρ.comp (MulEquiv.prodComm : GL b k × GL a k ≃* GL a k × GL b k).toMonoidHom)))) ∧ ∀ π : Representation ℂ (GL n k) V, Nonempty ((_root_.GlobalTheory.SmGL.jac₂Lower e π).Equiv ((_root_.GlobalTheory.SmGL.jac₂ ((Equiv.sumComm b a).trans e) π).comp (MulEquiv.prodComm : GL a k × GL b k ≃* GL b k × GL a k).toMonoidHom)) := by
  intro k _ _ _ _ a b n _ _ _ _ _ _ e V _ _
  refine ⟨fun ρ => ?_, fun π => ?_⟩
  · unfold _root_.GlobalTheory.SmGL.ind₂Lower _root_.GlobalTheory.SmGL.ind₂
      _root_.GlobalTheory.SmGL.parIndLower _root_.GlobalTheory.SmGL.parInd
    refine nonempty_equiv_smInd_of_eq (parabLower_eq_parab_sumComm k e) _ _
      fun g hg hg' => LinearMap.ext fun v => ?_
    simp only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.twist_apply,
      MulEquiv.coe_toMonoidHom]
    rw [leviProj_sumComm_eq_swap_leviProjLower k e ⟨g, hg⟩ hg', ← deltaHalf_inv_leviTwo_eq_deltaHalf_swap]
    simp
  · unfold _root_.GlobalTheory.SmGL.jac₂Lower _root_.GlobalTheory.SmGL.jac₂ _root_.GlobalTheory.SmGL.jacLower
      _root_.GlobalTheory.SmGL.jac _root_.GlobalTheory.SmGL.jacU
    rw [MonoidHom.comp_assoc]
    refine nonempty_equiv_twist_jacquet_comp π (unipRadLower_eq_unipRad_sumComm k e) _ _ _ _
      _ _ (fun x => leviEmb_leviTwo_eq_leviEmb_sumComm_swap k e x) _ _ fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MonoidHom.inv_apply, show (MulEquiv.prodComm x : GL b k × GL a k) = x.swap from rfl,
      ← deltaHalf_inv_leviTwo_eq_deltaHalf_swap, MonoidHom.inv_apply, inv_inv]

end GlobalTheory.SmGL.SwapBlocks
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory

namespace GlobalTheory.SmGL.Placing

section General

variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V]

def indLeft [TopologicalSpace G] [IsTopologicalGroup G] {P Q : Subgroup G}
    {σ : Representation F P V} {τ : Representation F Q V} (w : G)
    (h : ∀ q : Q, ∃ p : P, (p : G) = w * q * w⁻¹ ∧ σ p = τ q) :
    smoothPart (ind P σ) →ₗ[F] smoothPart (ind Q τ) where
  toFun f := ⟨⟨fun g => f.1.1 (w * g), fun q g => by
      obtain ⟨p, hp, hs⟩ := h q
      have : w * (q * g) = p * (w * g) := by rw [hp]; group
      show f.1.1 (w * (q * g)) = τ q (f.1.1 (w * g))
      rw [this, f.1.2 p, hs]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      (IsOpen.mem_nhds f.2 (by simp)) fun g hg => by
        have hg' : ind P σ g f.1 = f.1 := hg
        apply Subtype.ext
        funext x
        have := congrFun (congrArg Subtype.val hg') (w * x)
        show f.1.1 (w * (x * g)) = f.1.1 (w * x)
        rw [← mul_assoc]
        exact this)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


open ValuativeRel MeasureTheory in
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V] in
theorem _root_.GlobalTheory.SmGL.Placing.smInd_equiv [TopologicalSpace G] [IsTopologicalGroup G]
    {P Q : Subgroup G}
    {σ : Representation F P V} {τ : Representation F Q V} (w : G)
    (h : ∀ q : Q, ∃ p : P, (p : G) = w * q * w⁻¹ ∧ σ p = τ q)
    (h' : ∀ p : P, ∃ q : Q, (q : G) = w⁻¹ * p * w⁻¹⁻¹ ∧ τ q = σ p) :
    Nonempty ((_root_.GlobalTheory.PRep.smInd P σ).Equiv (_root_.GlobalTheory.PRep.smInd Q τ)) := by
  refine ⟨Representation.Equiv.mk
    { _root_.GlobalTheory.SmGL.Placing.indLeft w h with
      invFun := _root_.GlobalTheory.SmGL.Placing.indLeft w⁻¹ h'
      left_inv := fun f => ?_
      right_inv := fun f => ?_ } fun g => ?_⟩
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact congrArg f.1.1 (mul_inv_cancel_left w x)
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact congrArg f.1.1 (inv_mul_cancel_left w x)
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    exact congrArg f.1.1 (mul_assoc w x g)


open ValuativeRel MeasureTheory in
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V] in
lemma _root_.GlobalTheory.SmGL.Placing.twKer_le (π : Representation F G V)
    {N N' : Subgroup G} (w : G) (h : ∀ u ∈ N, w * u * w⁻¹ ∈ N') :
    _root_.GlobalTheory.PRep.twKer π N 1 ≤ (_root_.GlobalTheory.PRep.twKer π N' 1).comap (π w) := by
  unfold _root_.GlobalTheory.PRep.twKer
  rw [Submodule.span_le]
  rintro _ ⟨u, v, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  refine Submodule.subset_span ⟨⟨w * u * w⁻¹, h u u.2⟩, π w v, ?_⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, map_mul, Module.End.mul_apply]
  rw [← Module.End.mul_apply (π w⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]


open ValuativeRel MeasureTheory in
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V] in
theorem _root_.GlobalTheory.SmGL.Placing.jacquet_equiv (π : Representation F G V) {N N' : Subgroup G}
    {s s' : M →* G}
    (hs : ∀ g, s g ∈ Subgroup.normalizer (N : Set G))
    (hs' : ∀ g, s' g ∈ Subgroup.normalizer (N' : Set G)) (χ : M →* Fˣ) (w : G)
    (h : ∀ u ∈ N, w * u * w⁻¹ ∈ N') (h' : ∀ u ∈ N', w⁻¹ * u * w⁻¹⁻¹ ∈ N)
    (hw : ∀ g, w * s g * w⁻¹ = s' g) :
    Nonempty ((_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).Equiv
      (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N' s' hs') χ)) := by
  have hK := _root_.GlobalTheory.SmGL.Placing.twKer_le π w h
  have hK' := _root_.GlobalTheory.SmGL.Placing.twKer_le π w⁻¹ h'
  have hinv : ∀ a b : G, a * b = 1 → ∀ v, π a (π b v) = v := fun a b hab v => by
    rw [← Module.End.mul_apply, ← map_mul, hab, map_one, Module.End.one_apply]
  let eq : _root_.GlobalTheory.PRep.Jacquet π N ≃ₗ[F] _root_.GlobalTheory.PRep.Jacquet π N' :=
    LinearEquiv.ofLinear ((_root_.GlobalTheory.PRep.twKer π N 1).mapQ _ (π w) hK)
      ((_root_.GlobalTheory.PRep.twKer π N' 1).mapQ _ (π w⁻¹) hK')
      (Submodule.linearMap_qext _ (LinearMap.ext fun v => by
        simp [hinv w w⁻¹ (mul_inv_cancel w)]))
      (Submodule.linearMap_qext _ (LinearMap.ext fun v => by
        simp [hinv w⁻¹ w (inv_mul_cancel w)]))
  refine ⟨Representation.Equiv.mk eq fun g => ?_⟩
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (_root_.GlobalTheory.PRep.twKer π N 1) x
  have hv : π w (π (s g) v) = π (s' g) (π w v) := by
    rw [← hw g, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hinv w⁻¹ w (inv_mul_cancel w)]
  simp [eq, _root_.GlobalTheory.SmGL.twist, _root_.GlobalTheory.PRep.jacquet, hv]

end General

section Blocks

variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

def Moves {ι : Type} (e e' : ι ≃ n) (w : GL n R) : Prop :=
  ∀ (g : GL n R) x y, ((w * g * w⁻¹ : GL n R) : Matrix n n R) (e' x) (e' y) =
    (g : Matrix n n R) (e x) (e y)


open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.SmGL.Placing.exists_moves {ι : Type} (e e' : ι ≃ n) :
    ∃ w : GL n R, _root_.GlobalTheory.SmGL.Placing.Moves e e' w := by
  let σ : n ≃ n := e.symm.trans e'
  refine ⟨⟨σ.symm.toPEquiv.toMatrix, σ.toPEquiv.toMatrix, ?_, ?_⟩, fun g x y => ?_⟩
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  · simp [σ, Units.inv_mk, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]

variable {e e' : (Σ a, m a) ≃ n} {w : GL n R}



end Blocks

open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
private theorem moves_inv_of_moves {ι : Type} {e e' : ι ≃ n} {w : GL n R}
    (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w) : _root_.GlobalTheory.SmGL.Placing.Moves e' e w⁻¹ := by
  intro g x y
  have := hw (w⁻¹ * g * w⁻¹⁻¹) x y
  rw [← this]
  congr 2
  group

open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
private theorem conj_mem_parab_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    {g : GL n R} (hg : g ∈ _root_.GlobalTheory.SmGL.parab R e) :
    w * g * w⁻¹ ∈ _root_.GlobalTheory.SmGL.parab R e' := by
  have hg' : Matrix.BlockTriangular (g : Matrix n n R) (_root_.GlobalTheory.SmGL.blk e) := hg
  change Matrix.BlockTriangular _ (_root_.GlobalTheory.SmGL.blk e')
  intro i j hij
  obtain ⟨x, rfl⟩ := e'.surjective i
  obtain ⟨y, rfl⟩ := e'.surjective j
  rw [hw]
  exact hg' (by simpa [_root_.GlobalTheory.SmGL.blk] using hij)

open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
private theorem leviProj_conj_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    (p : _root_.GlobalTheory.SmGL.parab R e) :
    _root_.GlobalTheory.SmGL.leviProj R e' ⟨w * p * w⁻¹, conj_mem_parab_of_moves hw p.2⟩ =
      _root_.GlobalTheory.SmGL.leviProj R e p := by
  refine funext fun a => Units.ext (Matrix.ext fun i j => ?_)
  simpa [_root_.GlobalTheory.SmGL.leviProj, _root_.GlobalTheory.SmGL.diagBlock] using hw (p : GL n R) ⟨a, i⟩ ⟨a, j⟩

open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
private theorem conj_mem_unipRad_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    {u : GL n R} (hu : u ∈ _root_.GlobalTheory.SmGL.unipRad R e) :
    w * u * w⁻¹ ∈ _root_.GlobalTheory.SmGL.unipRad R e' := by
  have hP := _root_.GlobalTheory.SmGL.unipRad_le_parab R e hu
  have h1 := (_root_.GlobalTheory.SmGL.coe_mem_unipRad R (p := ⟨u, hP⟩)).1 hu
  exact (_root_.GlobalTheory.SmGL.coe_mem_unipRad R
    (p := ⟨w * u * w⁻¹, conj_mem_parab_of_moves hw hP⟩)).2
    ((leviProj_conj_of_moves hw ⟨u, hP⟩).trans h1)

open ValuativeRel MeasureTheory in
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {e e' : (Σ a, m a) ≃ n} {w : GL n R} in
private theorem leviEmb_conj_of_moves (hw : _root_.GlobalTheory.SmGL.Placing.Moves e e' w)
    (x : _root_.GlobalTheory.SmGL.Levi R m) :
    w * _root_.GlobalTheory.SmGL.leviEmb R e x * w⁻¹ = _root_.GlobalTheory.SmGL.leviEmb R e' x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨p, rfl⟩ := e'.surjective i
  obtain ⟨q, rfl⟩ := e'.surjective j
  rw [hw]
  simp [_root_.GlobalTheory.SmGL.leviEmb, Matrix.reindex_apply]


open ValuativeRel MeasureTheory in
theorem _root_.GlobalTheory.SmGL.Placing.parInd_jac_placing : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α]
    [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e e' : (Σ a, m a) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V],
    (∀ ρ : Representation ℂ (_root_.GlobalTheory.SmGL.Levi k m) V,
      Nonempty ((_root_.GlobalTheory.SmGL.parInd e ρ).Equiv (_root_.GlobalTheory.SmGL.parInd e' ρ))) ∧
    ∀ π : Representation ℂ (GL n k) V,
      Nonempty ((_root_.GlobalTheory.SmGL.jac e π).Equiv (_root_.GlobalTheory.SmGL.jac e' π)) := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e e' V _ _
  refine ⟨fun ρ => ?_, fun π => ?_⟩
  · obtain ⟨w, hw⟩ := _root_.GlobalTheory.SmGL.Placing.exists_moves (R := k) e' e
    have hw' := moves_inv_of_moves hw
    exact _root_.GlobalTheory.SmGL.Placing.smInd_equiv w
      (fun q => ⟨⟨_, conj_mem_parab_of_moves hw q.2⟩, rfl, by
        simp only [MonoidHom.comp_apply]
        rw [leviProj_conj_of_moves hw q]⟩)
      (fun p => ⟨⟨_, conj_mem_parab_of_moves hw' p.2⟩, rfl, by
        simp only [MonoidHom.comp_apply]
        rw [leviProj_conj_of_moves hw' p]⟩)
  · obtain ⟨w, hw⟩ := _root_.GlobalTheory.SmGL.Placing.exists_moves (R := k) e e'
    have hw' := moves_inv_of_moves hw
    exact _root_.GlobalTheory.SmGL.Placing.jacquet_equiv π _ _ _ w
      (fun u hu => conj_mem_unipRad_of_moves hw hu)
      (fun u hu => conj_mem_unipRad_of_moves hw' hu)
      (leviEmb_conj_of_moves hw)

end GlobalTheory.SmGL.Placing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeHeisenbergVariableSign
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.RootEx.HeisenbergSign

theorem colE_inv_eq {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (β : n → k) :
    ((colE c p β)⁻¹ : GL (n ⊕ Fin c) k).val = 1 - ((colE c p β).val - 1) := by
  rw [ExchangeSupport.colE_inv_val, ExchangeSupport.colE_val]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

theorem mat_add_gCol {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} (q : Fin c) (ξ : n → k) (x₀ : Matrix n n' k) (y : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k) :
    Exchange.mat x₀ (y + Exchange.gCol q ξ) = Exchange.mat x₀ y + colM c (q.val + 1) ξ := by
  ext r s
  rcases r with r | l <;> rcases s with s | i <;>
    simp [Exchange.mat, Exchange.gCol, colM, add_assoc, Fin.ext_iff]

theorem sign : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} → k) (β : n → k) (r : n) (i : Fin (c + 1)), i.val + 1 = ρ + 1 → ((1 - ((colE c (ρ + 1) β).val - 1)) * affPt (ρ + 1) x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (Sum.inl r) (Sum.inr i) = -β r) ∧ ∀ (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (β : n → k), (∀ x, om μ 1 (colE c (ρ + 1) β) Φ.1 x = Φ.1 ((1 - ((colE c (ρ + 1) β).val - 1)) * x)) ∧ ∀ x₀, fl ψ ν μ ρ Φ.1 x₀ β = opE ψ ν (ρ + 1) (fun x => Φ.1 (x + colM c (ρ + 1) (-β))) x₀ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ρ _ hρc
  refine ⟨fun x₀ e β r i hi => ?_, fun ψ ν _ hψ μ Φ β => ⟨fun x => ?_, fun x₀ => ?_⟩⟩
  ·
    have hi' : i = Fin.castSucc (⟨ρ, hρc⟩ : Fin c) := Fin.ext (by simp; omega)
    subst hi'
    have h := congrFun (Exchange.col_colE_inv_mul (n' := n') (⟨ρ, hρc⟩ : Fin c) β x₀ e) r
    simp only at h
    rw [← colE_inv_eq]
    exact neg_eq_iff_eq_neg.mp h
  · rw [Exchange.om_colE, colE_inv_eq]
  ·
    have hch : ∀ (y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (p : ℕ) (ξ : n → k),
        ch (y + colM c p ξ) = ch y := by
      intro y p ξ
      simp [ch, colM]
    have hmem : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
    have key := Exchange.opE_colE hψ ν μ (⟨ρ, hρc⟩ : Fin c) (⟨ρ, hρc⟩ : Fin c)
      (χ := fun _ => (1 : ℂ)) continuous_const hmem.1.continuous x₀ β
    dsimp only at key
    refine Eq.trans ?_ (key.trans ?_)
    · simp [fl]
    · rw [opE]
      congr 1
      funext e
      rw [mat_add_gCol, ← Exchange.affPt_eq]
      simp only [Exchange.big, one_mul, hch]

end GlobalTheory.RootEx.HeisenbergSign
end
end

