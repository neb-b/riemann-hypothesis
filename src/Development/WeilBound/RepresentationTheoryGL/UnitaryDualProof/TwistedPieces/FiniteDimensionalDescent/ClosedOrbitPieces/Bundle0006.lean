module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.Bundle0005

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.ExistsConj
section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrI

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.TP.Desc.Piece.Tr PositivityTheory.RgUd.TP.Desc.Piece.PTop

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

def lc {r : ℕ} (s : Fin r → Matrix (Fin N) (Fin N) k) (v : Fin r → k) : Matrix (Fin N) (Fin N) k := ∑ j, v j • s j

section Lc

variable {r : ℕ} (s : Fin r → Matrix (Fin N) (Fin N) k)

theorem lc_add (v w : Fin r → k) : lc s (v + w) = lc s v + lc s w := by
  simp only [lc, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem lc_sub (v w : Fin r → k) : lc s (v - w) = lc s v - lc s w := by
  simp only [lc, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem lc_smul (c : k) (v : Fin r → k) : lc s (c • v) = c • lc s v := by
  simp only [lc, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem lc_sum {ι : Type*} (T : Finset ι) (v : ι → Fin r → k) : lc s (∑ t ∈ T, v t) = ∑ t ∈ T, lc s (v t) := by
  simp only [lc, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem lc_single (j : Fin r) : lc s (Pi.single j 1) = s j := by
  simp [lc, Pi.single_apply]

theorem lc_mul (c : Fin r → Fin r → Fin r → k) (hmul : ∀ j j', s j * s j' = ∑ t, c j j' t • s t) (v w : Fin r → k) :
    lc s v * lc s w = lc s (fun t => ∑ j, ∑ j', v j * w j' * c j j' t) := by
  simp only [lc, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, hmul, Finset.smul_sum, smul_smul, Finset.sum_smul]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

end Lc

variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)

theorem sx_span {x : Matrix (Fin N) (Fin N) k} (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) :
    (Sx D x).toSubmodule = Submodule.span k (Set.range fun j => pe (D.a j) x) := by
  obtain ⟨hm, hu, -⟩ := D.spec x hx hχ
  set P := Submodule.span k (Set.range fun j => pe (D.a j) x) with hP
  have h1 : (1 : Matrix (Fin N) (Fin N) k) ∈ P := by
    rw [← hu]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hPP : P * P ≤ P := by
    rw [hP, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
    change pe (D.a i) x * pe (D.a j) x ∈ P
    rw [hm i j]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  have hmul : ∀ a b, a ∈ P → b ∈ P → a * b ∈ P := fun a b ha hb => hPP (Submodule.mul_mem_mul ha hb)
  apply le_antisymm
  · have hle : Algebra.adjoin k (Set.range fun j => pe (D.a j) x) ≤ P.toSubalgebra h1 hmul :=
      Algebra.adjoin_le Submodule.subset_span
    exact Subalgebra.toSubmodule.monotone hle
  · rw [Submodule.span_le]
    exact Algebra.subset_adjoin

private theorem lc_kappa_complete_orthogonal_primitive_idempotents {x : Matrix (Fin N) (Fin N) k} (hx : x ∈ Bz Z) (hχ : aeval x χ = 0)
    (s : Fin D.r → Matrix (Fin N) (Fin N) k) (hs : s = fun j => pe (D.a j) x) :
    (∀ j j', s j * s j' = ∑ t, D.c j j' t • s t) ∧ lc s D.u = 1 ∧
      (∀ j j', s j * s j' = s j' * s j) ∧
      (∀ y ∈ Submodule.span k (Set.range s), IsNilpotent y → y = 0) ∧
      (∀ t, IsIdempotentElem (lc s (D.κ t))) ∧
      ∑ t, lc s (D.κ t) = 1 ∧
      (∀ t t', t ≠ t' → lc s (D.κ t) * lc s (D.κ t') = 0) ∧
      (∀ t, ∀ y ∈ Submodule.span k (Set.range s), IsIdempotentElem y →
        y * lc s (D.κ t) = y → y = 0 ∨ y = lc s (D.κ t)) ∧
      (∀ v, lc s v = 0 ↔ ∀ t, lc s (D.κ t) ≠ 0 → v ∈ D.K t) := by
  subst hs
  obtain ⟨h1, h2, h3, -, -, h6, -, -, h9, h10, h11, h12, -, h14⟩ := D.spec x hx hχ
  exact ⟨h1, h2, h3, h6, h9, h10, h11, h12, h14⟩

theorem exists_isAttachedHodgeS_conj_mapRep (hO : OrbHom k) (hZ : CR Z) {τ : Fin D.m → ℕ} {x₀ x : Matrix (Fin N) (Fin N) k}
    (h₀ : x₀ ∈ piece D τ) (h : x ∈ piece D τ) :
    ∃ g : GL (Fin N) k, ∀ j, pe (D.a j) x = cj g (pe (D.a j) x₀) := by
  classical
  obtain ⟨hx₀B, hx₀χ, hx₀τ⟩ := h₀
  obtain ⟨hxB, hxχ, hxτ⟩ := h
  set s0 : Fin D.r → Matrix (Fin N) (Fin N) k := fun j => pe (D.a j) x₀ with hs0
  set s : Fin D.r → Matrix (Fin N) (Fin N) k := fun j => pe (D.a j) x with hs
  obtain ⟨m0, u0, c0, n0, i0, hsum0, o0, prim0, k0⟩ := lc_kappa_complete_orthogonal_primitive_idempotents D hx₀B hx₀χ s0 hs0
  obtain ⟨m1, u1, -, -, i1, -, o1, -, k1⟩ := lc_kappa_complete_orthogonal_primitive_idempotents D hxB hxχ s hs
  have hr0 : ∀ t, (lc s0 (D.κ t)).rank = τ t := fun t => congrFun hx₀τ t
  have hr1 : ∀ t, (lc s (D.κ t)).rank = τ t := fun t => congrFun hxτ t
  have hne : ∀ t, lc s0 (D.κ t) ≠ 0 ↔ lc s (D.κ t) ≠ 0 := by
    intro t
    rw [ne_zero_iff_rank, ne_zero_iff_rank, hr0, hr1]
  have hker : ∀ v, lc s0 v = 0 ↔ lc s v = 0 := by
    intro v
    rw [k0, k1]
    exact forall_congr' fun t => imp_congr_left (hne t)
  have hspan0 := sx_span D hx₀B hx₀χ
  have memSpan : ∀ y, y ∈ Sx D x₀ ↔ y ∈ Submodule.span k (Set.range s0) := by
    intro y
    rw [← Subalgebra.mem_toSubmodule, hspan0]
  have memS : ∀ y, y ∈ Sx D x₀ ↔ ∃ v, lc s0 v = y := by
    intro y
    rw [memSpan, Submodule.mem_span_range_iff_exists_fun]
    rfl
  have hcomm : ∀ a ∈ Sx D x₀, ∀ b ∈ Sx D x₀, a * b = b * a := by
    intro a ha b hb
    obtain ⟨v, rfl⟩ := (memS a).1 ha
    obtain ⟨w, rfl⟩ := (memS b).1 hb
    simp only [lc, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      congrArg₂ (· • ·) (mul_comm _ _) (c0 _ _)
  have hred : IsReduced (Sx D x₀) := by
    refine ⟨fun a ha => Subtype.ext ?_⟩
    exact n0 a.1 ((memSpan a.1).1 a.2) (ha.map (Sx D x₀).val)
  letI : CommRing (Sx D x₀) := cr_commRing ⟨hcomm, hred⟩
  choose vOf hvOf using fun a : Sx D x₀ => (memS a.1).1 a.2
  have key : ∀ (a : Sx D x₀) v, lc s0 v = a.1 → lc s (vOf a) = lc s v := by
    intro a v hv
    have h0 : lc s0 (vOf a - v) = 0 := by rw [lc_sub, hvOf, hv, sub_self]
    rw [← sub_eq_zero, ← lc_sub]
    exact (hker _).1 h0
  let F : Sx D x₀ →ₗ[k] Matrix (Fin N) (Fin N) k :=
    { toFun := fun a => lc s (vOf a)
      map_add' := fun a b => by
        show lc s (vOf (a + b)) = lc s (vOf a) + lc s (vOf b)
        rw [key (a + b) (vOf a + vOf b) (by rw [lc_add, hvOf, hvOf]; rfl), lc_add]
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        rw [key (c • a) (c • vOf a) (by rw [lc_smul, hvOf]; rfl), lc_smul] }
  let ρ' : Sx D x₀ →ₐ[k] Matrix (Fin N) (Fin N) k := AlgHom.ofLinearMap F
    (by
      show lc s (vOf 1) = 1
      rw [key 1 D.u (by rw [u0]; rfl), u1])
    (fun a b => by
      show lc s (vOf (a * b)) = lc s (vOf a) * lc s (vOf b)
      rw [lc_mul s D.c m1, key (a * b) (fun t => ∑ j, ∑ j', vOf a j * vOf b j' * D.c j j' t)
        (by rw [← lc_mul s0 D.c m0 (vOf a) (vOf b), hvOf, hvOf]; rfl)])
  have hρ' : ∀ a, ρ' a = lc s (vOf a) := fun a => rfl
  have hEmem : ∀ t, lc s0 (D.κ t) ∈ Sx D x₀ := fun t => (memS _).2 ⟨_, rfl⟩
  have hrk : ∀ e : Sx D x₀, IsIdempotentElem e → ((Sx D x₀).val e).rank = (ρ' e).rank := by
    intro e he
    have he1 : IsIdempotentElem e.1 := congrArg Subtype.val he
    have hpart : ∀ t, e.1 * lc s0 (D.κ t) = 0 ∨ e.1 * lc s0 (D.κ t) = lc s0 (D.κ t) := by
      intro t
      have hc : Commute e.1 (lc s0 (D.κ t)) := hcomm _ e.2 _ (hEmem t)
      refine prim0 t _ ((memSpan _).1 (Subalgebra.mul_mem _ e.2 (hEmem t)))
        (IsIdempotentElem.mul_of_commute hc he1 (i0 t)) ?_
      rw [mul_assoc, (i0 t).eq]
    set T' := Finset.univ.filter (fun t => e.1 * lc s0 (D.κ t) ≠ 0) with hT'
    have hfe : e.1 = ∑ t ∈ T', lc s0 (D.κ t) := by
      rw [hT', Finset.sum_filter]
      conv_lhs => rw [← mul_one e.1, ← hsum0, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs with h'
      · rcases hpart t with h | h
        · exact absurd h h'
        · exact h
      · exact not_not.1 h'
    have hrep : lc s0 (∑ t ∈ T', D.κ t) = e.1 := by
      rw [lc_sum]
      exact hfe.symm
    have r0 : (∑ t ∈ T', lc s0 (D.κ t)).rank = ∑ t ∈ T', (lc s0 (D.κ t)).rank :=
      (rank_sum_orth (fun t => lc s0 (D.κ t)) i0 o0 T').2
    have r1 : (∑ t ∈ T', lc s (D.κ t)).rank = ∑ t ∈ T', (lc s (D.κ t)).rank :=
      (rank_sum_orth (fun t => lc s (D.κ t)) i1 o1 T').2
    show e.1.rank = (lc s (vOf e)).rank
    rw [key e _ hrep, lc_sum, r1]
    conv_lhs => rw [hfe]
    rw [r0]
    simp only [hr0, hr1]
  obtain ⟨g, hg⟩ := hO N (Sx D x₀) hred (Sx D x₀).val ρ' hrk
  refine ⟨g, fun j => ?_⟩
  have hmem : s0 j ∈ Sx D x₀ := (memS _).2 ⟨Pi.single j 1, lc_single s0 j⟩
  have e1 := hg ⟨s0 j, hmem⟩
  rw [hρ', key _ (Pi.single j 1) (lc_single s0 j), lc_single] at e1
  exact e1

end PositivityTheory.RgUd.TP.Desc.Piece.TrI
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TefFinrank
section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece Module

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0)
  {e f : Matrix (Fin N) (Fin N) k} (he : e ∈ primIdem (Sx D x)) (hf : f ∈ primIdem Z) (hef : e * f = e)
include hZ hx hχ he hf hef

theorem tef_nil {w : Matrix (Fin N) (Fin N) k} (hw : w ∈ Tef (Z := Z) e f) (hn : IsNilpotent w) : w = 0 := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  simp only [LinearMap.mulLeft_apply] at hn ⊢
  rw [tef_zero hZ hx he.2.1 he.2.2.1 hf hef (sx_le D he.1) hz hn, mul_zero]

theorem tef_finrank : finrank k (Tef (Z := Z) e f) = finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f)) := by
  have hinj : Function.Injective ((LinearMap.mulLeft k e).comp
      (Submodule.subtype (Z.toSubmodule.map (LinearMap.mulLeft k f)))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨y, hy⟩ h0
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.mulLeft_apply] at h0
    have hfz := tef_zero hZ hx he.2.1 he.2.2.1 hf hef (sx_le D he.1) hz (by rw [h0]; exact IsNilpotent.zero)
    apply Subtype.ext
    simpa using hfz
  have h := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_comp, Submodule.range_subtype] at h
  exact h

theorem tef_inf : Tef (Z := Z) e f ⊓ Nx D x = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  exact tef_nil D hZ hx hχ he hf hef hw.1 (nx_nil D hZ hx hχ w hw.2)

theorem tef_le : Tef (Z := Z) e f ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨s, hs, n, hn, rfl⟩ := Submodule.mem_sup.1 (z_le D hZ hx hχ hz)
  simp only [LinearMap.mulLeft_apply]
  have hfS : f ∈ Sx D x := pz_mem_S D hZ hx hχ hf
  have hfC : f ∈ Cx Z x := z_le_cx hf.1
  have heC : e ∈ Cx Z x := sx_le D he.1
  have hs' : s ∈ Sx D x := (Subalgebra.mem_toSubmodule _).1 hs
  rw [mul_add, mul_add]
  refine Submodule.add_mem_sup (Submodule.mem_map.2 ⟨f * s, (Subalgebra.mem_toSubmodule _).2 ((Sx D x).mul_mem hfS hs'), rfl⟩) ?_
  rw [← mul_assoc]
  exact nx_mul D hZ hx (e * f) ((Cx Z x).mul_mem heC hfC) n hn

theorem dim_le : finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f)) ≤
    finrank k ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) := by
  rw [← tef_finrank D hZ hx hχ he hf hef]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Tef (Z := Z) e f) (Nx D x)
  rw [tef_inf D hZ hx hχ he hf hef, finrank_bot, add_zero] at h1
  have h2 : Tef (Z := Z) e f ⊔ Nx D x ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x :=
    sup_le (tef_le D hZ hx hχ he hf hef) le_sup_right
  have h3 := Submodule.finrank_mono h2
  have h4 := Submodule.finrank_add_le_finrank_add_finrank
    ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) (Nx D x)
  omega

theorem dim_eq_le (hd : finrank k ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) ≤
    finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f))) :
    (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ≤ Tef (Z := Z) e f ⊔ Nx D x := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Tef (Z := Z) e f) (Nx D x)
  rw [tef_inf D hZ hx hχ he hf hef, finrank_bot, add_zero, tef_finrank D hZ hx hχ he hf hef] at h1
  have h2 : Tef (Z := Z) e f ⊔ Nx D x ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x :=
    sup_le (tef_le D hZ hx hχ he hf hef) le_sup_right
  have h4 := Submodule.finrank_add_le_finrank_add_finrank
    ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) (Nx D x)
  have h5 := Submodule.eq_of_le_of_finrank_le h2 (by omega)
  rw [h5]
  exact le_sup_left

end

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0)
include hZ hx hχ

theorem zn_of_eq (h : ∀ f ∈ primIdem Z, f ∈ primIdem (Sx D x) ∧
      finrank k ((Sx D x).toSubmodule.map (LinearMap.mulLeft k f)) ≤ finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f))) :
    ∃ c ∈ Z, IsNilpotent (x - c) := by
  have hfin := pi_fin hZ
  have hS : (Sx D x).toSubmodule ≤ Z.toSubmodule ⊔ Nx D x := by
    intro s hs
    have hsum : s = ∑ f ∈ hfin.toFinset, f * s := by
      rw [← Finset.sum_mul, pi_sum hZ, one_mul]
    rw [hsum]
    refine Submodule.sum_mem _ (fun f hf => ?_)
    rw [Set.Finite.mem_toFinset] at hf
    obtain ⟨hfS, hd⟩ := h f hf
    have hle := dim_eq_le D hZ hx hχ hfS hf hfS.2.1.eq hd
    have hmem : f * s ∈ (Sx D x).toSubmodule.map (LinearMap.mulLeft k f) :=
      Submodule.mem_map.2 ⟨s, hs, rfl⟩
    have hT : Tef (Z := Z) f f ≤ Z.toSubmodule ⊔ Nx D x := by
      intro w hw
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
      apply Submodule.mem_sup_left
      simp only [LinearMap.mulLeft_apply]
      exact (Subalgebra.mem_toSubmodule _).2 (Z.mul_mem hf.1 (Z.mul_mem hf.1 hz))
    exact (sup_le hT le_sup_right) (hle hmem)
  have hxm : x ∈ Z.toSubmodule ⊔ Nx D x :=
    (sup_le hS le_sup_right : (Sx D x).toSubmodule ⊔ Nx D x ≤ _) (x_mem D hZ hx hχ)
  obtain ⟨c, hc, n, hn, hcn⟩ := Submodule.mem_sup.1 hxm
  refine ⟨c, hc, ?_⟩
  rw [← hcn, add_sub_cancel_left]
  exact nx_nil D hZ hx hχ n hn

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

