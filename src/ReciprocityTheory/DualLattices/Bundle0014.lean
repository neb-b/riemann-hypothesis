module

public import ReciprocityTheory.DualLattices.DvdOfCoeffZero
public import ReciprocityTheory.DualLattices.ValUntiltESubOne
public import ReciprocityTheory.DualLattices.Bundle0006
public import ReciprocityTheory.DualLattices.Bundle0012
public import ReciprocityTheory.DualLattices.Bundle0005
public import ReciprocityTheory.DualLattices.Bundle0011
public import ReciprocityTheory.DualLattices.Bundle0010
public import ReciprocityTheory.DualLattices.Bundle0004
public import ReciprocityTheory.DualLattices.Bundle0007
public import ReciprocityTheory.DualLattices.Bundle0009

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.Imports
section
namespace ReciprocityTheory.PGsh

theorem a0 (p : ℕ) [Fact p.Prime] : TiltStructureStatement p := by
  intro C _ _ _ v O _ _ hv _ _
  have hK : KerThetaStatement p O := kerTheta (p := p) (C := C) (v := v) (O := O) hv
  have hO : ∀ x : O, (p : O) * x = 0 → x = 0 := by
    intro x hx
    have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
    have h1 := congrArg (algebraMap O C) hx
    rw [map_mul, map_natCast, map_zero] at h1
    apply hv.hom_inj
    rw [map_zero]
    exact (mul_eq_zero.mp h1).resolve_left hp0
  obtain ⟨pf, hpf⟩ := exists_pflat (p := p) (hv := hv)
  exact ⟨⟨pf, hpf⟩, exists_eps (p := p) (hv := hv), hK,
    xiNu p C v O hK, regular (p := p) (O := O) (hO := hO), flatW' (p := p) (O := O)⟩

end ReciprocityTheory.PGsh
end

-- bundled from ReciprocityTheory.DualLattices.LenIdStatement
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

def qE {R : Type} [CommRing R] {g m : ℕ} (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :
    Submodule R (Fin g ⊕ Fin g → R) :=
  (LinearMap.range (Matrix.mulVecLin (εL j)ᵀ)).comap (LinearMap.funLeft R R Sum.inl) ⊓
    (LinearMap.range (Matrix.mulVecLin (εL i))).comap (LinearMap.funLeft R R Sum.inr)

abbrev xModE {R : Type} [CommRing R] {g m : ℕ} (Ht Bt : Matrix (Fin g) (Ix g) R)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)) (i : Fin m) :=
  qE εL i (π i) ⧸
    ((LinearMap.range (Matrix.mulVecLin (εT i))).map (Matrix.mulVecLin (fromRows Ht Bt))).comap
      (qE εL i (π i)).subtype

def LenIdStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) R) (E : Matrix (Ix g) (Ix g) R)
    (cp : R), cp ≠ 0 → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E →
    ∀ (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)), (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) → (∀ i, Bt * εT i = εL i * Bt) →
    (∀ i, (εT i)ᵀ * E = E * εT (π i)) →
    ∀ (i : Fin m) (d : ℕ), Nonempty (LinearMap.range (Matrix.mulVecLin (εL i)) ≃ₗ[R] (Fin d → R)) →
    ∀ c₁ c₂ : NNReal, HasLen v R (cokE Ht εT εL i (π i)) c₁ →
      HasLen v R (cokE Ht εT εL (π i) i) c₂ →
      ∃ X : NNReal, HasLen v R (xModE Ht Bt εT εL π i) X ∧ X * c₁ = v (algebraMap R C cp) ^ d * c₂

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.LinPairStatement
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

structure OEnd (B : BX R₀) (O : LAlg R₀) where
  f : ∀ {R : LAlg R₀}, LHom O R → B.G R →+ B.G R
  nat : ∀ {R S : LAlg R₀} (s : LHom O R) (g : LHom R S) (x : B.G R),
    f (g.comp s) (B.map g x) = B.map g (f s x)

structure OAdj (B : BX R₀) (O : LAlg R₀) where
  a : OEnd B O
  ab : OEnd B O
  e : ∀ {R : LAlg R₀} (s : LHom O R) (x z : B.G R), B.P R (a.f s x) z ≃ B.P R x (ab.f s z)
  e_smul : ∀ {R : LAlg R₀} (s : LHom O R) (x z : B.G R) (l : (R : Type u)ˣ) (u : B.P R (a.f s x) z),
    e s x z (B.smul l u) = B.smul l (e s x z u)
  equiv_addFst : ∀ {R : LAlg R₀} (s : LHom O R) (x x' z : B.G R) (u : B.P R (a.f s x) z)
    (u' : B.P R (a.f s x') z),
    e s (x + x') z (B.tr1 (map_add (a.f s) x x').symm (B.add1 u u')) =
      B.add1 (e s x z u) (e s x' z u')
  equiv_addSnd : ∀ {R : LAlg R₀} (s : LHom O R) (x z z' : B.G R) (u : B.P R (a.f s x) z)
    (w : B.P R (a.f s x) z'),
    e s x (z + z') (B.add2 u w) =
      B.tr2 (map_add (ab.f s) z z').symm (B.add2 (e s x z u) (e s x z' w))

namespace DualPair

variable {R : LAlg R₀} (Dp : DualPair R)

lemma ση_mem (r : (R : Type u)) : Dp.σ.1 r * Dp.η ∈ Dp.π.ker := by
  rw [LHom.ker, Submodule.restrictScalars_mem, Dp.ker_eq]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

def ηmap : (R : Type u) →ₗ[R₀] Dp.π.ker where
  toFun r := ⟨Dp.σ.1 r * Dp.η, Dp.ση_mem r⟩
  map_add' r r' := Subtype.ext (by simp [add_mul])
  map_smul' c r := Subtype.ext (by simp [Algebra.smul_def, mul_assoc])

end DualPair

def hext (B : BX R₀) {R : LAlg R₀} (h : B.gg →ₗ[R₀] (R : Type u)) : B.gg ⊗[R₀] (R : Type u) →ₗ[R₀] (R : Type u) :=
  LinearMap.mul' R₀ (R : Type u) ∘ₗ TensorProduct.map h LinearMap.id

def LinHtStatement (B : BX R₀) (O : LAlg R₀) : Prop :=
  ∀ (A : OAdj B O) (R : LAlg R₀) (s : LHom O R) (Dp : DualPair R) (N : ℕ) (y : B.G R)
    (h : B.gg →ₗ[R₀] (R : Type u)) (δ : B.gg →ₗ[R₀] B.gg ⊗[R₀] (R : Type u)),
    N • y = 0 → B.IsHeight Dp N y h →
    (∀ v, A.ab.f (Dp.σ.comp s) (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap (δ v))) →
    B.IsHeight Dp N (A.a.f s y) (hext B h ∘ₗ δ)

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.MemDualLatMapFourier
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def tableM (e : H ≃ AddChar N C) (σ : H ≃ N) : Matrix N N C :=
  Matrix.of fun x j => e (σ.symm j) x

theorem tableM_isUnit (e : H ≃ AddChar N C) (σ : H ≃ N) : IsUnit (tableM e σ).det := by
  unfold tableM
  exact charTable_isUnit (σ.symm.trans e)

private theorem fourier_column_eq (e : H ≃ AddChar N C) (σ : H ≃ N) (Dm : Matrix N N C) (h : H)
    (j : N) :
    fourier (R := R) (fun h a => e h a) (fun x => Dm x j) h =
      ((tableM e σ)ᵀ * Dm) (σ h) j := by
  simp only [fourier_apply', Matrix.mul_apply, Matrix.transpose_apply, tableM,
    Matrix.of_apply, Equiv.symm_apply_apply]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem map_fourier_spanCols (e : H ≃ AddChar N C) (σ : H ≃ N) (Dm : Matrix N N C) :
    (Submodule.span R (Set.range fun j x => Dm x j)).map (fourier (R := R) fun h a => e h a) =
      Submodule.span R (Set.range fun k h => ((tableM e σ)ᵀ * Dm).submatrix σ σ h k) := by
  rw [Submodule.map_span]
  congr 1
  ext f
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    refine ⟨σ.symm j, ?_⟩
    funext h
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
    exact (fourier_column_eq e σ Dm h j).symm
  · rintro ⟨k, rfl⟩
    refine ⟨_, ⟨σ k, rfl⟩, ?_⟩
    funext h
    simp only [Matrix.submatrix_apply]
    exact fourier_column_eq e σ Dm h (σ k)

private theorem addChar_apply_ne_zero_dual_lattices (ψ : AddChar N C) (a : N) : ψ a ≠ 0 := by
  intro h0
  have h1 : ψ a * ψ (-a) = 1 := by
    rw [← AddChar.map_add_eq_mul]
    simp
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

theorem e_zero (e : H ≃ AddChar N C) (he : ∀ h h', e (h + h') = e h * e h') : e 0 = 1 := by
  have h0 := he 0 0
  rw [add_zero] at h0
  ext a
  have ha : e 0 a = e 0 a * e 0 a := by
    have := congrArg (fun ψ : AddChar N C => ψ a) h0
    simpa only [AddChar.mul_apply] using this
  rw [AddChar.one_apply]
  exact mul_left_cancel₀ (addChar_apply_ne_zero_dual_lattices (e 0) a) (by rw [mul_one]; exact ha.symm)

theorem e_neg_apply (e : H ≃ AddChar N C) (he : ∀ h h', e (h + h') = e h * e h') (h : H) (a : N) :
    e (-h) a = e h (-a) := by
  have h1 := he (-h) h
  have hz : -h + h = 0 := by simp
  rw [hz, e_zero e he] at h1
  have h2 := congrArg (fun ψ : AddChar N C => ψ a) h1
  simp only [AddChar.mul_apply, AddChar.one_apply] at h2
  have h3 : e h (-a) * e h a = 1 := by
    rw [← AddChar.map_add_eq_mul]
    simp
  exact mul_right_cancel₀ (addChar_apply_ne_zero_dual_lattices (e h) a) (h2.symm.trans h3.symm)

private theorem mem_dualLat_iff_pairing_integral {X : Type} [Fintype X] {M : Submodule R (X → C)} {u : X → C} :
    u ∈ dualLat M ↔ ∀ f ∈ M, ∃ r : R, algebraMap R C r = ∑ a, u a * f a := Iff.rfl

theorem antipode_fourier (e : H ≃ AddChar N C) (he : ∀ h h', e (h + h') = e h * e h')
    (AA : HopfOrder (C := C) R N) (u : N → C) (hu : u ∈ dualLat AA.carrier) :
    (fun x => fourier (R := R) (fun h a => e h a) u (-x)) ∈
      (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a) := by
  rw [Submodule.mem_map]
  refine ⟨fun a => u (-a), ?_, ?_⟩
  · rw [mem_dualLat_iff_pairing_integral]
    intro f hf
    obtain ⟨r, hr⟩ := (mem_dualLat_iff_pairing_integral.1 hu) (fun x => f (-x)) (AA.antipode f hf)
    refine ⟨r, hr.trans ?_⟩
    exact Fintype.sum_equiv (Equiv.neg N) _ _ (fun a => by simp)
  · funext x
    simp only [fourier_apply']
    exact Fintype.sum_equiv (Equiv.neg N) _ _ (fun a => by simp [e_neg_apply e he])

theorem char_expand (e : H ≃ AddChar N C) (B : Matrix N N C) (hB : IsUnit B.det) (h : H) (a : N) :
    e h a = ∑ i, fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) h * B a i := by
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  symm
  calc ∑ i, fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) h * B a i
      = ∑ i, ∑ x, B a i * B⁻¹ i x * e h x := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [fourier_apply', Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = ∑ x, ∑ i, B a i * B⁻¹ i x * e h x := Finset.sum_comm
    _ = ∑ x, (B * B⁻¹) a x * e h x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Matrix.mul_apply, Finset.sum_mul]
    _ = e h a := by simp [hBB, Matrix.one_apply]

private theorem mem_intFun_iff_pairing {X : Type} {f : X → C} :
    f ∈ intFun (C := C) R X ↔ ∀ x, ∃ r : R, algebraMap R C r = f x := Iff.rfl

theorem comul_fourier (e : H ≃ AddChar N C) (he : ∀ h h', e (h + h') = e h * e h')
    (AA : HopfOrder (C := C) R N) (B : Matrix N N C) (hB : IsUnit B.det)
    (hAA : AA.carrier = Submodule.span R (Set.range fun j x => B x j))
    (u : N → C) (hu : u ∈ dualLat AA.carrier) :
    addPull R H (fourier (R := R) (fun h a => e h a) u) ∈
      tensorSpan R ((dualLat AA.carrier).map (fourier (R := R) fun h a => e h a)) := by
  have hg : ∀ i, (fun a => u a * B a i) ∈ dualLat AA.carrier := by
    intro i
    rw [mem_dualLat_iff_pairing_integral]
    intro f hf
    have hcol : (fun x => B x i) ∈ AA.carrier := by
      rw [hAA]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨r, hr⟩ := (mem_dualLat_iff_pairing_integral.1 hu) _ (AA.mul_mem _ _ hcol hf)
    refine ⟨r, hr.trans (Finset.sum_congr rfl fun a _ => ?_)⟩
    simp only [Pi.mul_apply]
    ring
  have hk : ∀ i, (fun x => B⁻¹ i x) ∈ dualLat AA.carrier := by
    intro i
    rw [hAA, mem_dualLat_spanCols_iff, mem_intFun_iff_pairing]
    intro j
    show ∃ r : R, algebraMap R C r = (B⁻¹ * B) i j
    rw [Matrix.nonsing_inv_mul B hB, Matrix.one_apply]
    by_cases hij : i = j
    · exact ⟨1, by simp [hij]⟩
    · exact ⟨0, by simp [hij]⟩
  have hsplit : addPull R H (fourier (R := R) (fun h a => e h a) u) =
      ∑ i, fun p : H × H => fourier (R := R) (fun h a => e h a) (fun a => u a * B a i) p.1 *
        fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := by
    funext p
    rw [Finset.sum_apply]
    simp only [addPull, LinearMap.funLeft_apply]
    calc fourier (R := R) (fun h a => e h a) u (p.1 + p.2)
        = ∑ a, u a * e p.1 a *
            ∑ i, fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 * B a i := by
          rw [fourier_apply' (R := R) (fun h a => e h a) u (p.1 + p.2)]
          refine Finset.sum_congr rfl fun a _ => ?_
          show u a * e (p.1 + p.2) a = _
          rw [he, AddChar.mul_apply, char_expand (R := R) e B hB p.2 a]
          ring
      _ = ∑ a, ∑ i, u a * B a i * e p.1 a *
            fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = ∑ i, ∑ a, u a * B a i * e p.1 a *
            fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := Finset.sum_comm
      _ = ∑ i, fourier (R := R) (fun h a => e h a) (fun a => u a * B a i) p.1 *
            fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [fourier_apply' (R := R) (fun h a => e h a) (fun a => u a * B a i) p.1, Finset.sum_mul]
  rw [hsplit]
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_
  exact ⟨_, Submodule.mem_map_of_mem (hg i), _, Submodule.mem_map_of_mem (hk i), rfl⟩

theorem pairing_fourier (e : H ≃ AddChar N C) (w : H → C) (u : N → C) :
    ∑ h, w h * fourier (R := R) (fun h a => e h a) u h =
      ∑ a, fourier (R := R) (fun a h => e h a) w a * u a := by
  simp only [fourier_apply', Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem mem_dualLat_map_fourier (e : H ≃ AddChar N C) (M : Submodule R (N → C)) (w : H → C) :
    w ∈ dualLat (M.map (fourier (R := R) fun h a => e h a)) ↔
      fourier (R := R) (fun a h => e h a) w ∈ dualLat M := by
  rw [mem_dualLat_iff_pairing_integral, mem_dualLat_iff_pairing_integral]
  constructor
  · intro hw f hf
    obtain ⟨r, hr⟩ := hw _ (Submodule.mem_map_of_mem hf)
    exact ⟨r, hr.trans (pairing_fourier (R := R) e w f)⟩
  · intro hw g hg
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hg
    obtain ⟨r, hr⟩ := hw f hf
    exact ⟨r, hr.trans (pairing_fourier (R := R) e w f).symm⟩

theorem fourier'_surjective (e : H ≃ AddChar N C) (σ : H ≃ N) (f : N → C) :
    ∃ w, fourier (R := R) (fun a h => e h a) w = f := by
  have hM := tableM_isUnit e σ
  refine ⟨fun h => ((tableM e σ)⁻¹ *ᵥ f) (σ h), ?_⟩
  funext a
  simp only [fourier_apply']
  calc ∑ x, ((tableM e σ)⁻¹ *ᵥ f) (σ x) * e x a
      = ∑ j, tableM e σ a j * ((tableM e σ)⁻¹ *ᵥ f) j :=
        Fintype.sum_equiv σ _ _ fun x => by
          simp only [tableM, Matrix.of_apply, Equiv.symm_apply_apply]
          ring
    _ = (tableM e σ *ᵥ ((tableM e σ)⁻¹ *ᵥ f)) a := rfl
    _ = f a := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]

end ReciprocityTheory.PGsh.L2
end
end

-- bundled from ReciprocityTheory.DualLattices.MemMapAugmentationIdealComapPullbackQuotient
section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem apply_add_of_mem_map_pullbackQuotient (K : AddSubgroup N) (M : Submodule R (N ⧸ K → C)) {h : N → C}
    (hh : h ∈ M.map (pullQ (R := R) K)) (x : N) (k : K) : h (x + k) = h x := by
  obtain ⟨u, -, rfl⟩ := hh
  simp only [pullQ, LinearMap.funLeft_apply]
  rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).mpr k.2, add_zero]

theorem pullbackQuotient_apply_out (K : AddSubgroup N) {h : N → C} (hinv : ∀ x (k : K), h (x + k) = h x) :
    pullQ (R := R) K (fun q => h q.out) = h := by
  funext x
  simp only [pullQ, LinearMap.funLeft_apply]
  have e : (((QuotientAddGroup.mk x : N ⧸ K).out : N) : N ⧸ K) = (x : N ⧸ K) := by
    exact Quotient.out_eq _
  have hk := QuotientAddGroup.eq.mp e
  calc h (QuotientAddGroup.mk x : N ⧸ K).out
      = h ((QuotientAddGroup.mk x : N ⧸ K).out + ((⟨_, hk⟩ : K) : N)) := (hinv _ _).symm
    _ = h x := by congr 1; simp

theorem mem_map_comap_pullbackQuotient (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) {h : N → C}
    (hh : h ∈ AA.carrier) (hinv : ∀ x (k : K), h (x + k) = h x) :
    h ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ (R := R) K) := by
  refine Submodule.mem_map.mpr ⟨fun q => h q.out, ?_, pullbackQuotient_apply_out (R := R) K hinv⟩
  rw [Submodule.mem_comap, pullbackQuotient_apply_out (R := R) K hinv]
  exact hh

theorem mem_map_augmentationIdeal_comap_pullbackQuotient (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) {h : N → C}
    (hh : h ∈ AA.carrier) (hinv : ∀ x (k : K), h (x + k) = h x) (h0 : h 0 = 0) :
    h ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) := by
  refine Submodule.mem_map.mpr ⟨fun q => h q.out, ?_, pullbackQuotient_apply_out (R := R) K hinv⟩
  simp only [augIdeal, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [Submodule.mem_comap, pullbackQuotient_apply_out (R := R) K hinv]
    exact hh
  · have h1 := congrFun (pullbackQuotient_apply_out (R := R) K hinv) 0
    simp only [pullQ, LinearMap.funLeft_apply, QuotientAddGroup.mk_zero] at h1
    simp only [LinearMap.mem_ker, LinearMap.proj_apply]
    rw [h1, h0]

section family

variable (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
  [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
  (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
  (f : K → N → C) (hf : ∀ j, f j ∈ AA.carrier) (hdet : ∀ x, v (h3mm K β f x).det = 1)

include hβ hdet in
theorem eq_zero_of_sum_mul_coset_eq_zero (x : N) (c : K → C) (h : ∀ k : K, ∑ j, c j * f j (x + k) = 0) : c = 0 := by
  have hM : (h3mm K β f x).det ≠ 0 := by
    intro h0
    have := hdet x
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hw : β *ᵥ (c ᵥ* h3mm K β f x) = 0 := by
    funext k
    rw [Pi.zero_apply, ← h k]
    have e : ∀ j, f j (x + k) = ∑ l, β k l * h3mm K β f x j l := fun j => by
      rw [cosetCoordinates_expand K β hβ (f j) x k]
      rfl
    simp only [e]
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hw0 : c ᵥ* h3mm K β f x = 0 := by
    have := congrArg (β⁻¹ *ᵥ ·) hw
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul β hβ] using this
  by_contra hc
  exact hM (Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, hc, hw0⟩)

include hv hβ hAK hf hdet in
theorem exists_coset_invariant_coefficients {g : N → C} (hg : g ∈ AA.carrier) :
    ∃ b : K → N → C, (∀ j, b j ∈ AA.carrier) ∧ (∀ j x (k : K), b j (x + k) = b j x) ∧
      g = ∑ j, b j * f j := by
  have hDne : ∀ x, (h3mm K β f x).det ≠ 0 := fun x h0 => by
    have := hdet x
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hFu : ∀ x, IsUnit (h3mm K β f x).det := fun x =>
    isUnit_iff_ne_zero.mpr (hDne x)
  obtain ⟨b, hb⟩ : ∃ b : K → N → C, b = fun j x =>
      (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) j := ⟨_, rfl⟩
  have hbx : ∀ j x, b j x = (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) j :=
    fun j x => by rw [hb]
  let Fm : Matrix K K (N → C) := Matrix.of fun i j => fun x => h3co K β (f i) x j
  have hFm : ∀ i j, Fm i j ∈ AA.carrier := fun i j =>
    cosetCoordinates_mem AA K β hβ hAK (hf i) j
  have hDA := det_mem_and_adjugate_mem AA Fm hFm
  have hD : (fun x => (h3mm K β f x).det) ∈ AA.carrier := hDA.1
  have hAdj : ∀ l j, (fun x => (h3mm K β f x).adjugate l j) ∈ AA.carrier :=
    hDA.2
  obtain ⟨P, hP, hA⟩ := AA.lat
  have hDinv : (fun x => (h3mm K β f x).det)⁻¹ ∈ AA.carrier :=
    inv_mem_of_valuation_eq_one hv AA.carrier P hP hA AA.one_mem AA.mul_mem _ hD hdet
  have hG : ∀ l, (fun x => h3co K β g x l) ∈ AA.carrier := fun l =>
    cosetCoordinates_mem AA K β hβ hAK hg l
  refine ⟨b, ?_, ?_, ?_⟩
  · intro j
    have key : b j = (∑ l, (fun x => h3co K β g x l) *
        (fun x => (h3mm K β f x).adjugate l j)) *
        (fun x => (h3mm K β f x).det)⁻¹ := by
      funext x
      rw [hbx, Matrix.inv_def]
      simp only [Pi.mul_apply, Finset.sum_apply, Pi.inv_apply, Matrix.vecMul, dotProduct,
        Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Ring.inverse_eq_inv]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [key]
    exact AA.mul_mem _ _ (Submodule.sum_mem _ fun l _ => AA.mul_mem _ _ (hG l) (hAdj l j)) hDinv
  · intro j x k
    have hT : IsUnit (h3T K β k).det := by
      refine isUnit_iff_ne_zero.mpr fun h0 => hDne (x + k) ?_
      rw [cosetCoordinateMatrix_add K β hβ f x k, Matrix.det_mul, h0, mul_zero]
    rw [hbx, hbx, cosetCoordinates_add K β hβ g x k, cosetCoordinateMatrix_add K β hβ f x k,
      Matrix.mul_inv_rev, Matrix.vecMul_vecMul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hT, Matrix.one_mul]
  · funext x
    have e1 := cosetCoordinates_expand K β hβ g x 0
    have e2 := fun j => cosetCoordinates_expand K β hβ (f j) x 0
    rw [show ((0 : K) : N) = 0 from rfl, add_zero] at e1
    simp only [show ((0 : K) : N) = 0 from rfl, add_zero] at e2
    have hv' : (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) ᵥ*
        h3mm K β f x = h3co K β g x := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hFu x), Matrix.vecMul_one]
    have hw : ∀ l, ∑ j, (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) j *
        h3co K β (f j) x l = h3co K β g x l := fun l => by
      have := congrFun hv' l
      exact this
    rw [Finset.sum_apply]
    simp only [Pi.mul_apply, hbx, e2]
    rw [e1]
    generalize h3co K β g x ᵥ* (h3mm K β f x)⁻¹ = w at hw ⊢
    simp only [← hw]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end family

end ReciprocityTheory.PGsh.L2
end
end

