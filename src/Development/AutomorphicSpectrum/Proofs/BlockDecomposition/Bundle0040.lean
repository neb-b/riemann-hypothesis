module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.GapAbsOf
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRiemannRochSpaceIffRegularAtEverywhere
section
noncomputable section

open Matrix Classical PositivityTheory.Rg.Rs

namespace GlobalTheory.CompanionTheory.GLFirstBasisOrbit

variable {k : Type} [Field k] {n : ℕ}

theorem mem_gmap {N : ℕ} (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) (x : Fin N → k) :
    x ∈ gmap g M ↔ (g⁻¹).val *ᵥ x ∈ M := by
  unfold gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
    exact hz
  · intro h
    refine ⟨_, h, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]

theorem smul_mem_gmap {N : ℕ} (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) (x : Fin N → k) :
    g.val *ᵥ x ∈ gmap g M ↔ x ∈ M := by
  rw [mem_gmap, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem gmap_mul {N : ℕ} (g h : GL (Fin N) k) (M : Submodule k (Fin N → k)) :
    gmap (g * h) M = gmap g (gmap h M) := by
  ext x
  rw [mem_gmap, mem_gmap, mem_gmap, Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev]

theorem gmap_one {N : ℕ} (M : Submodule k (Fin N → k)) : gmap (1 : GL (Fin N) k) M = M := by
  ext x
  rw [mem_gmap, inv_one, Units.val_one, Matrix.one_mulVec]

theorem gmap_top {N : ℕ} (g : GL (Fin N) k) : gmap g ⊤ = ⊤ := by
  ext x
  simp [mem_gmap]

def gmapEquiv {N : ℕ} (g : GL (Fin N) k) : Submodule k (Fin N → k) ≃ Submodule k (Fin N → k) where
  toFun := gmap g
  invFun := gmap g⁻¹
  left_inv M := by rw [← gmap_mul, inv_mul_cancel, gmap_one]
  right_inv M := by rw [← gmap_mul, mul_inv_cancel, gmap_one]

theorem finrank_gmap {N : ℕ} (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) :
    Module.finrank k (gmap g M) = Module.finrank k M := by
  have hinj : Function.Injective (Matrix.toLin' g.val) := by
    intro x y h
    have := congrArg (fun z => (g⁻¹).val *ᵥ z) h
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using this
  exact (Submodule.equivMapOfInjective _ hinj M).finrank_eq.symm

theorem first_basis_ne_zero : e0 k n ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [e0] at this

theorem star_e0_dotProduct (x : Fin (n + 1) → k) : e0 k n ⬝ᵥ x = x 0 := by
  simp [e0]

theorem mem_riemannRochSpace_iff_regularAt_everywhere (x : Fin (n + 1) → k) : x ∈ H0 k n ↔ x 0 = 0 := by
  simp [H0]

theorem exists_GL_first_basis_eq (x : Fin (n + 1) → k) (hx : x ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, g.val *ᵥ e0 k n = x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) k := (1 : Matrix _ _ k).updateCol i x
  have hA : A.det = x i := by
    have := Matrix.cramer_apply (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) x i
    rw [← show (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol i x = A from rfl, ← this]
    simp
  let G : Matrix (Fin (n + 1)) (Fin (n + 1)) k := A.submatrix id (Equiv.swap 0 i)
  have hG : G.det ≠ 0 := by
    have := Matrix.det_permute' (Equiv.swap 0 i) A
    rw [show G = A.submatrix id (Equiv.swap 0 i) from rfl, this, hA]
    refine mul_ne_zero ?_ hi
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (n + 1)) i)) with h | h <;> rw [h] <;> simp
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero G hG, ?_⟩
  ext a
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, e0, G, A]

theorem exists_gl_cov (a : Fin (n + 1) → k) (ha : a ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, ∀ x, a ⬝ᵥ (g.val *ᵥ x) = x 0 := by
  obtain ⟨h, hh⟩ := exists_GL_first_basis_eq a ha
  have hd : (h.val)ᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnits_det_units h).ne_zero
  let T : GL (Fin (n + 1)) k := Matrix.GeneralLinearGroup.mkOfDetNeZero (h.val)ᵀ hd
  refine ⟨T⁻¹, fun x => ?_⟩
  have hT : T.val = (h.val)ᵀ := rfl
  have h1 : a = e0 k n ᵥ* T.val := by rw [hT, Matrix.vecMul_transpose, hh]
  rw [Matrix.dotProduct_mulVec, h1, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.vecMul_one, star_e0_dotProduct]

theorem mem_GL_image_hyperplane_iff (g : GL (Fin (n + 1)) k) (a : Fin (n + 1) → k)
    (h : ∀ x, a ⬝ᵥ (g.val *ᵥ x) = x 0) (z : Fin (n + 1) → k) :
    z ∈ gmap g (H0 k n) ↔ a ⬝ᵥ z = 0 := by
  rw [mem_gmap, mem_riemannRochSpace_iff_regularAt_everywhere, ← h ((g⁻¹).val *ᵥ z), Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mulVec]

theorem exists_scalar_stabilizer_line (g : GL (Fin (n + 1)) k)
    (h : gmap g (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n}) :
    ∃ s : k, s ≠ 0 ∧ g.val *ᵥ e0 k n = s • e0 k n := by
  have h1 : g.val *ᵥ e0 k n ∈ Submodule.span k {e0 k n} := by
    rw [← h, smul_mem_gmap]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp h1
  refine ⟨s, ?_, hs.symm⟩
  rintro rfl
  have h2 : g.val *ᵥ e0 k n = 0 := by rw [← hs, zero_smul]
  have h3 := congrArg (fun z => (g⁻¹).val *ᵥ z) h2
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h3
  exact first_basis_ne_zero h3

section Lat

variable {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]

def stabV (red : Γ →* GL (Fin (n + 1)) k) (ρ : Γ →* Module.End ℂ V) : Submodule ℂ V where
  carrier := {y | ∀ γ, gmap (red γ) (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n} → ρ γ y = y}
  add_mem' := by
    intro a b ha hb γ h
    rw [map_add (f := _), ha γ h, hb γ h]
  zero_mem' := by
    intro γ _
    simp
  smul_mem' := by
    intro c a ha γ h
    rw [map_smul, ha γ h]

theorem mem_stabV (red : Γ →* GL (Fin (n + 1)) k) (ρ : Γ →* Module.End ℂ V) (y : V) :
    y ∈ stabV red ρ ↔
      ∀ γ, gmap (red γ) (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n} → ρ γ y = y := Iff.rfl

variable [Fintype k]

def zx (v : Submodule k (Fin (n + 1) → k) → V) (x : Fin (n + 1) → k) (j : ℕ) : V :=
  ∑ M ∈ Finset.univ.filter (fun M : Submodule k (Fin (n + 1) → k) => x ∈ M ∧ Module.finrank k M + j = n + 1), v M

def IsCov (red : Γ →* GL (Fin (n + 1)) k) (gam : (Fin (n + 1) → k) → Γ) : Prop :=
  ∀ a, a ≠ 0 → ∀ x, a ⬝ᵥ ((red (gam a)).val *ᵥ x) = x 0

def uop (ρ : Γ →* Module.End ℂ V) (t : Module.End ℂ V) (gam : (Fin (n + 1) → k) → Γ) : Module.End ℂ V :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1), ρ (gam a) * t

end Lat

end GlobalTheory.CompanionTheory.GLFirstBasisOrbit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
section
noncomputable section

namespace GlobalTheory.CompanionTheory.TwistedAverage

open GlobalTheory.PRep

section Coset

variable {H V : Type} [Group H] [AddCommGroup V]

theorem sum_out_refine {N K : Subgroup H} (hNK : N ≤ K) [Fintype (H ⧸ N)] [Fintype (H ⧸ K)]
    [Fintype (K ⧸ N.subgroupOf K)] (f : H → V) (hf : ∀ x, ∀ k ∈ K, f (x * k) = f x) :
    ∑ q : H ⧸ N, f q.out = Fintype.card (K ⧸ N.subgroupOf K) • ∑ q : H ⧸ K, f q.out := by
  have h1 : ∀ q : H ⧸ N, f q.out = f ((Subgroup.quotientEquivProdOfLE hNK q).1).out := by
    intro q
    have hq : (Subgroup.quotientEquivProdOfLE hNK q).1 = (QuotientGroup.mk q.out : H ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K q.out
    rw [hh, hf _ _ h.2]
  calc ∑ q : H ⧸ N, f q.out
      = ∑ q : H ⧸ N, f ((Subgroup.quotientEquivProdOfLE hNK q).1).out :=
        Finset.sum_congr rfl fun q _ => h1 q
    _ = ∑ p : (H ⧸ K) × (K ⧸ N.subgroupOf K), f p.1.out :=
        Equiv.sum_comp (Subgroup.quotientEquivProdOfLE hNK) (fun p => f p.1.out)
    _ = Fintype.card (K ⧸ N.subgroupOf K) • ∑ q : H ⧸ K, f q.out := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ]
        rw [Finset.smul_sum]

theorem sum_out_mul_right (N : Subgroup H) [N.Normal] [Fintype (H ⧸ N)] (f : H → V)
    (hf : ∀ x, ∀ k ∈ N, f (x * k) = f x) (l : H) :
    ∑ q : H ⧸ N, f (q.out * l) = ∑ q : H ⧸ N, f q.out := by
  have h1 : ∀ q : H ⧸ N, f (q.out * l) = f (q * (QuotientGroup.mk l : H ⧸ N)).out := by
    intro q
    have hq : q * (QuotientGroup.mk l : H ⧸ N) = QuotientGroup.mk (q.out * l) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [hq]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N (q.out * l)
    rw [hh, hf _ _ h.2]
  calc ∑ q : H ⧸ N, f (q.out * l)
      = ∑ q : H ⧸ N, f (q * (QuotientGroup.mk l : H ⧸ N)).out :=
        Finset.sum_congr rfl fun q _ => h1 q
    _ = ∑ q : H ⧸ N, f q.out :=
        Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk l : H ⧸ N)) (fun q => f q.out)

end Coset

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def twOrbit (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V) (t : L) : V :=
  (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ (t : G) x

def stabKer (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V) : Subgroup L where
  carrier := {l | ρ (l : G) x = x ∧ θ l = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, by rw [map_mul, ha', hb', one_mul]⟩
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, by rw [map_inv, ha', inv_one]⟩
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

theorem twOrbit_mul_right (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V)
    (t k : L) (hk : k ∈ stabKer ρ L θ x) : twOrbit ρ L θ x (t * k) = twOrbit ρ L θ x t := by
  obtain ⟨h1, h2⟩ := hk
  simp only [twOrbit]
  rw [map_mul, h2, mul_one, Subgroup.coe_mul, map_mul, Module.End.mul_apply, h1]

theorem twOrbit_gen (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (w : V) (l t : L) :
    twOrbit ρ L θ (ρ (l : G) w - (θ l : ℂ) • w) t =
      (θ l : ℂ) • (twOrbit ρ L θ w (t * l) - twOrbit ρ L θ w t) := by
  simp only [twOrbit]
  have h : (θ l : ℂ) * (((θ (t * l))⁻¹ : ℂˣ) : ℂ) = (((θ t)⁻¹ : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, map_mul, mul_inv, mul_comm (θ t)⁻¹, mul_inv_cancel_left]
  rw [smul_sub, smul_smul, h, Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub, map_smul,
    smul_sub, smul_smul, smul_smul, mul_comm]

theorem twOrbit_add (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x y : V) (t : L) :
    twOrbit ρ L θ (x + y) t = twOrbit ρ L θ x t + twOrbit ρ L θ y t := by
  simp only [twOrbit, map_add (f := _), smul_add]

theorem twOrbit_smul (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (c : ℂ) (x : V)
    (t : L) : twOrbit ρ L θ (c • x) t = c • twOrbit ρ L θ x t := by
  simp only [twOrbit, map_smul]
  rw [smul_comm]

section Top

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isOpen_stabKer {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (L : Subgroup G)
    (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (x : V) :
    IsOpen (stabKer ρ L θ x : Set L) := by
  have h1 : IsOpen {l : L | ρ (l : G) x = x} := (hρ x).preimage continuous_subtype_val
  have h2 : (stabKer ρ L θ x : Set L) = {l : L | ρ (l : G) x = x} ∩ (θ.ker : Set L) := by
    ext l
    simp [stabKer, MonoidHom.mem_ker]
  rw [h2]
  exact h1.inter hθ

theorem finiteIndex_stabKer {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (x : V) :
    (stabKer ρ L θ x).FiniteIndex := by
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  haveI : Finite (L ⧸ stabKer ρ L θ x) :=
    Subgroup.quotient_finite_of_isOpen _ (isOpen_stabKer hρ L θ hθ x)
  exact Subgroup.finiteIndex_of_finite_quotient

theorem exists_sum_eq_zero {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) {v : V}
    (hv : v ∈ twKer ρ L θ) :
    ∃ M : Subgroup L, M.FiniteIndex ∧ ∀ (N : Subgroup L) [N.Normal] [Fintype (L ⧸ N)], N ≤ M →
      ∑ q : L ⧸ N, twOrbit ρ L θ v q.out = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, w, rfl⟩ := hx
    refine ⟨stabKer ρ L θ w, finiteIndex_stabKer hρ hL θ hθ w, ?_⟩
    intro N _ _ hN
    have hf : ∀ x, ∀ k ∈ N, twOrbit ρ L θ w (x * k) = twOrbit ρ L θ w x :=
      fun x k hk => twOrbit_mul_right ρ L θ w x k (hN hk)
    simp only [twOrbit_gen]
    rw [← Finset.smul_sum, Finset.sum_sub_distrib,
      sum_out_mul_right N (twOrbit ρ L θ w) hf l, sub_self, smul_zero]
  | zero =>
    refine ⟨⊤, inferInstance, ?_⟩
    intro N _ _ _
    simp [twOrbit]
  | add x y _ _ hx hy =>
    obtain ⟨M₁, h₁, s₁⟩ := hx
    obtain ⟨M₂, h₂, s₂⟩ := hy
    refine ⟨M₁ ⊓ M₂, inferInstance, ?_⟩
    intro N _ _ hN
    simp only [twOrbit_add]
    rw [Finset.sum_add_distrib, s₁ N (hN.trans inf_le_left), s₂ N (hN.trans inf_le_right), add_zero]
  | smul c x _ hx =>
    obtain ⟨M, h, s⟩ := hx
    refine ⟨M, h, ?_⟩
    intro N _ _ hN
    simp only [twOrbit_smul]
    rw [← Finset.smul_sum, s N hN, smul_zero]

theorem mem_twKer_iff_average (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (L : Subgroup G)
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (v : V) :
    v ∈ twKer ρ L θ ↔ ∃ (K : Subgroup L) (T : Finset L), IsOpen (K : Set L) ∧
      (∀ x ∈ K, ρ (x : G) v = v) ∧ (∀ x ∈ K, θ x = 1) ∧
      (∀ x : L, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K) ∧
      ∑ t ∈ T, (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ t v = 0 := by
  classical
  constructor
  · intro hv
    obtain ⟨M, hM, hsum⟩ := exists_sum_eq_zero hρ hL θ hθ hv
    haveI hK : (stabKer ρ L θ v).FiniteIndex := finiteIndex_stabKer hρ hL θ hθ v
    haveI : Fintype (L ⧸ stabKer ρ L θ v) := Fintype.ofFinite _
    refine ⟨stabKer ρ L θ v, (Finset.univ : Finset (L ⧸ stabKer ρ L θ v)).image Quotient.out,
      isOpen_stabKer hρ L θ hθ v,
      fun x hx => hx.1, fun x hx => hx.2, ?_, ?_⟩
    · intro x
      refine ⟨(QuotientGroup.mk x : L ⧸ stabKer ρ L θ v).out, ⟨Finset.mem_image_of_mem _
        (Finset.mem_univ _), ?_⟩, ?_⟩
      · exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
      · rintro t ⟨ht, hx⟩
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
        have : q = (QuotientGroup.mk x : L ⧸ stabKer ρ L θ v) := by
          rw [← QuotientGroup.out_eq' q]
          exact QuotientGroup.eq.2 hx
        rw [this]
    · rw [Finset.sum_image (fun a _ b _ h => Quotient.out_injective h)]
      set C : Subgroup L := (M ⊓ stabKer ρ L θ v).normalCore with hC
      haveI : C.Normal := Subgroup.normalCore_normal _
      haveI : C.FiniteIndex := inferInstance
      haveI : Fintype (L ⧸ C) := Fintype.ofFinite _
      have hCM : C ≤ M ⊓ stabKer ρ L θ v := Subgroup.normalCore_le _
      haveI : Finite (stabKer ρ L θ v ⧸ C.subgroupOf (stabKer ρ L θ v)) := inferInstance
      haveI : Fintype (stabKer ρ L θ v ⧸ C.subgroupOf (stabKer ρ L θ v)) := Fintype.ofFinite _
      have h0 := hsum C (hCM.trans inf_le_left)
      rw [sum_out_refine (hCM.trans inf_le_right) (twOrbit ρ L θ v)
        (fun x k hk => twOrbit_mul_right ρ L θ v x k hk)] at h0
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
      rcases h0 with h0 | h0
      · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
      · exact h0
  · rintro ⟨K, T, -, -, -, hT, hsum⟩
    have hne : T.Nonempty := by
      obtain ⟨t, ⟨ht, -⟩, -⟩ := hT 1
      exact ⟨t, ht⟩
    have hc : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne.card_pos.ne'
    have hmem : ∀ t : L, v - (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ (t : G) v ∈ twKer ρ L θ := by
      intro t
      have hg : ρ (t : G) v - (θ t : ℂ) • v ∈ twKer ρ L θ := Submodule.subset_span ⟨t, v, rfl⟩
      have := (twKer ρ L θ).smul_mem (-(((θ t)⁻¹ : ℂˣ) : ℂ)) hg
      convert this using 1
      rw [smul_sub, smul_smul, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, neg_smul,
        neg_smul, one_smul]
      abel
    have hs : (T.card : ℂ) • v = ∑ t ∈ T, (v - (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ (t : G) v) := by
      rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Nat.cast_smul_eq_nsmul]
    have h1 : (T.card : ℂ) • v ∈ twKer ρ L θ := hs ▸ Submodule.sum_mem _ fun t _ => hmem t
    exact ((twKer ρ L θ).smul_mem_iff hc).1 h1

end Top

end GlobalTheory.CompanionTheory.TwistedAverage
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityFinitePlaces
section
open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.WedgeMinor

theorem det_mul_submatrix_expand {K ι ι' κ : Type} [CommRing K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) (t : κ → ι') :
    ((g * A).submatrix t id).det =
      ∑ s : κ → ι, (∏ i, g (t i) (s i)) * (A.submatrix s id).det := by
  have h : ((g * A).submatrix t id : κ → κ → K) = fun i => ∑ k, g (t i) k • A k := by
    funext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  have key : ∀ M : Matrix κ κ K,
      M.det = (detRowAlternating (R := K) (n := κ)).toMultilinearMap M := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, h, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem sz_nonneg {K ι κ : Type} [NormedField K] (g : Matrix ι κ K) : 0 ≤ sz g :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem le_sz {K ι κ : Type} [NormedField K] [Finite ι] [Finite κ] (g : Matrix ι κ K)
    (i : ι) (j : κ) : ‖g i j‖ ≤ sz g :=
  le_ciSup (f := fun p : ι × κ => ‖g p.1 p.2‖) (Set.finite_range _).bddAbove (i, j)

theorem nF_nonneg {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem le_nF {K ι κ : Type} [NormedField K] [Finite ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (s : κ → ι) : ‖(A.submatrix s id).det‖ ≤ nF A :=
  le_ciSup (f := fun s : κ → ι => ‖(A.submatrix s id).det‖) (Set.finite_range _).bddAbove s

theorem norm_minor_mul_le {K ι ι' κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι]
    [Fintype ι'] [Fintype κ] [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) (t : κ → ι') :
    ‖((g * A).submatrix t id).det‖ ≤ sz g ^ Fintype.card κ * nF A := by
  rw [det_mul_submatrix_expand]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (pow_nonneg (sz_nonneg g) _) (nF_nonneg A)) fun s _ => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_mul ?_ (le_nF A s) (norm_nonneg _) (pow_nonneg (sz_nonneg g) _)
  calc ∏ i, ‖g (t i) (s i)‖ ≤ ∏ _i : κ, sz g :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => le_sz g _ _
    _ = sz g ^ Fintype.card κ := by simp

theorem nF_mul_le {K ι ι' κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι]
    [Fintype ι'] [Fintype κ] [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) :
    nF (g * A) ≤ sz g ^ Fintype.card κ * nF A :=
  Real.iSup_le (fun t => norm_minor_mul_le g A t)
    (mul_nonneg (pow_nonneg (sz_nonneg g) _) (nF_nonneg A))

theorem nF_mul_right {K ι κ : Type} [NormedField K] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (s : Matrix κ κ K) : nF (A * s) = nF A * ‖s.det‖ := by
  unfold nF
  rw [Real.iSup_mul_of_nonneg (norm_nonneg _)]
  refine iSup_congr fun t => ?_
  have h : (A * s).submatrix t id = A.submatrix t id * s := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h, det_mul, norm_mul]

theorem nF_square {K κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ]
    (s : Matrix κ κ K) : nF s = ‖s.det‖ := by
  refine le_antisymm (Real.iSup_le (fun t => ?_) (norm_nonneg _)) ?_
  · by_cases ht : Function.Injective t
    · have hb : Function.Bijective t := Finite.injective_iff_bijective.mp ht
      have h := Matrix.det_permute (Equiv.ofBijective t hb) s
      have h' : (s.submatrix t id).det = _ := h
      rw [h', norm_mul]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective t hb)) with h1 | h1 <;>
        simp [h1]
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, t i = t j ∧ i ≠ j := by
        simpa [Function.Injective] using ht
      rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hij])]
      simp
  · simpa using le_nF s id

theorem mulF : MulF := by
  intro K ι ι' κ _ _ _ _ _ _ A
  exact ⟨fun g => nF_mul_le g A, fun s => nF_mul_right A s, fun s => nF_square s⟩

end GlobalTheory.CompanionTheory.WedgeMinor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneTmulMemRangeIff
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovCmp

theorem one_tmul_mem_range_iff {A : Type} [CommRing A] (B' : Type) [CommRing B'] [Algebra A B']
    {K₁ K₀ : Type} [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀]
    (d : K₁ →ₗ[A] K₀) (z : K₀) :
    ((1 : B') ⊗ₜ[A] z) ∈ LinearMap.range (d.lTensor B') ↔
      (1 : B') ⊗ₜ[A] ((LinearMap.range d).mkQ z) = 0 := by
  have hex := lTensor_exact B' (LinearMap.exact_map_mkQ_range d)
    (Submodule.mkQ_surjective (LinearMap.range d))
  have := hex ((1 : B') ⊗ₜ[A] z)
  rw [LinearMap.lTensor_tmul] at this
  exact this.symm

theorem cov_of_solv : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A), (∀ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Solv B a c → ∃ (B₁ : Type) (_ : CommRing B₁) (_ : Algebra A B₁), Cov p r B₁ ∧ Solv B₁ a c) → Cov p r B := by
  intro p _ A _ B _ _ r h K₁ K₀ _ _ _ _ h₁ h₀ d hd z hz k
  have hB := (one_tmul_mem_range_iff B d z).mp hz
  obtain ⟨m, n, a, c, hs, hall⟩ := GlobalTheory.CompanionTheory.EqCrit.exists_system B ((LinearMap.range d).mkQ z) hB
  obtain ⟨B₁, i₁, i₂, hc, hs₁⟩ := h m n a c hs
  have h0 := hall B₁ hs₁
  exact hc K₁ K₀ h₁ h₀ d hd z ((one_tmul_mem_range_iff B₁ d z).mpr h0) k

end GlobalTheory.CompanionTheory.CovCmp
end

